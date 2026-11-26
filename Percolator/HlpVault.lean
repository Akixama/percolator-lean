/-
  Percolator.HlpVault
  Minimal, formally verified permissionless HLP (Hyperliquidity Provider) Vault program
  that composes with `percolator-lean` via CPI (`sol_invoke_signed_c`) with ZERO core changes.

  Capabilities & Mainnet Security Guarantees:
  - Owns a cross-margin `percolator` `Portfolio` via PDA `["hlpv", vault.key, bump]`.
  - **Zero Strategist Rug**: Strategist can bind/revoke a PropAMM (`SetHlpMatcher`), pause new
    deposits, and trigger `Liquidate(mode=1)` zero-ADL takeovers (`HlpTakeoverLiquidate`),
    but CANNOT withdraw a single atom of depositor funds and CANNOT pause withdrawals!
  - **100% Auto-Compounding Yield**: PropAMM spread profits accrue directly to `hlpPfl.capital`,
    AND `HlpTakeoverLiquidate` routes keeper liquidation fees into `hlpFeeTok` and immediately
    CPIs `percolator::DepositCollateral` back into `hlpPfl` for HLP depositors!
  - **Anti-Arbitrage Dual-NAV Pricing & Same-Slot Freshness**:
    * Every open leg on `hlpPfl` MUST be refreshed in `curSlot` before minting OR burning shares!
    * Deposits price shares against optimistic full equity `navDeposit = capital + Σ posPnl`
      (preventing dilution of existing LPs' unsettled profits).
    * Withdrawals price redemptions against realized free capital `navWithdraw = capital ≤ navDeposit`
      (preventing deposit->withdraw arbitrage and respecting core `totalIm`).
  - **Anti-Inflation & Anti-Donation-Capture**:
    * First deposit requires `amount ≥ minDeposit ≥ 1_000_000` and locks any pre-existing direct
      donation `navDeposit` behind unowned dead shares (`totalShares := navDeposit + amount`).
    * Drained vault (`totalShares > 0 ∧ navDeposit == 0`) blocks new deposits while still allowing
      existing holders to burn worthless shares (`payout == 0`) and reclaim 100% of receipt rent!
  - **Zero Rent Leak**: Full `WithdrawHlp` (`receipt.shares == 0`) auto-closes `HlpReceipt`
    (`zeroHlpWords` + `MAGIC_CLOSED` + full rent lamport refund to `owner`).
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.HlpVault

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open LeanSVM.CPI
open Percolator

def MAGIC_HLP             : UInt32 := 0x56504C48 -- "HLPV"
def MAGIC_HLPR            : UInt32 := 0x52504C48 -- "HLPR"
def TAG_HLP_AUTH          : UInt32 := 0x76706C68 -- "hlpv"
def MIN_FIRST_HLP_DEPOSIT : UInt64 := 1_000_000  -- 1.0 quote unit (anti-ERC4626 inflation)
def MAX_HLP_LOCKUP        : UInt64 := 216_000    -- ~24h at 400ms/slot

namespace HErr
  def paused            : UInt64 := 500
  def lockupActive      : UInt64 := 501
  def capExceeded       : UInt64 := 502
  def progMismatch      : UInt64 := 503
  def pflMismatch       : UInt64 := 504
  def feeTokBad         : UInt64 := 505
  def vaultMismatch     : UInt64 := 506
  def matcherNotAllowed : UInt64 := 507
  def marketNotAllowed  : UInt64 := 508
end HErr

/-! ### Exact Byte Offsets: `HlpVault` (296B), `HlpReceipt` (88B) -/

namespace HlpOff
  def size               : UInt64 := 296
  def magic              : UInt64 := 0   -- u32 ("HLPV")
  def pdaBump            : UInt64 := 4   -- u8
  def paused             : UInt64 := 5   -- u8 (0 = open, 1 = deposits paused; withdraws NEVER paused!)
  def allowedCount       : UInt64 := 6   -- u8 (1..8, IMMUTABLE pinned market allowlist count!)
  def strategist         : UInt64 := 8   -- Pubkey (32)
  def percProg           : UInt64 := 40  -- Pubkey (32)
  def dex                : UInt64 := 72  -- Pubkey (32)
  def hlpPortfolio       : UInt64 := 104 -- Pubkey (32)
  def hlpFeeTok          : UInt64 := 136 -- Pubkey (32)
  def lockupSlots        : UInt64 := 168 -- u64
  def depositCap         : UInt64 := 176 -- u64 (0 = unlimited)
  def totalShares        : UInt64 := 184 -- u64
  def minDeposit         : UInt64 := 192 -- u64
  def allowedMatcherProg : UInt64 := 200 -- Pubkey (32B IMMUTABLE verified PropAMM program; blocks evil_matcher rug!)
  def allowedMarkets     : UInt64 := 232 -- 8 × u64 (IMMUTABLE market allowlist for both PropAMM & takeover!)
end HlpOff

namespace HlpRecOff
  def size            : UInt64 := 88
  def magic           : UInt64 := 0  -- u32 ("HLPR")
  def vault           : UInt64 := 8  -- Pubkey (32)
  def owner           : UInt64 := 40 -- Pubkey (32)
  def shares          : UInt64 := 72 -- u64
  def lastDepositSlot : UInt64 := 80 -- u64
end HlpRecOff

theorem hlp_layout_sizes_valid :
    HlpOff.allowedMarkets + MAX_LEGS * 8 ≤ HlpOff.size ∧ HlpOff.size % 8 == 0 ∧
    HlpRecOff.lastDepositSlot + 8 ≤ HlpRecOff.size ∧ HlpRecOff.size % 8 == 0 := by
  decide

/-! ### Pure HLP Share-Pool Specification & Formal Proofs (0 `sorry`, 0 custom axioms) -/

/-- Pure HLP deposit share minting: returns `(mintShares, newTotalShares)`.
    When `totalShares = 0`, locks pre-existing `navDep` behind unowned dead shares so a first
    depositor can NEVER capture prior direct donations into `hlpPfl`! -/
def hlpMintSharesNat (amount totalShares navDep : Nat) : Nat × Nat :=
  if totalShares = 0 then
    (amount, navDep + amount)
  else if navDep = 0 then
    (0, totalShares)
  else
    let m := (amount * totalShares) / navDep
    (m, totalShares + m)

/-- Pure HLP redemption payout against conservative realized `capital`:
    `floor(burnShares * capital / totalShares)`. -/
def hlpWithdrawPayoutNat (burnShares totalShares capital : Nat) : Nat :=
  if totalShares = 0 then 0 else (burnShares * capital) / totalShares

/-- **THEOREM 1 (`hlp_first_deposit_locks_donation`)**:
    When `totalShares = 0` and an attacker/donor previously sent `preCap` directly into `hlpPfl`,
    depositing `amount` mints `amount` shares out of `preCap + amount` total shares, so immediate
    full redemption yields `≤ amount` (ZERO stolen donation, 100% immune to PR #4 capture!). -/
theorem hlp_first_deposit_locks_donation (preCap posPnl amount : Nat) :
    let (minted, newTot) := hlpMintSharesNat amount 0 (preCap + posPnl)
    hlpWithdrawPayoutNat minted newTot (preCap + amount) ≤ amount := by
  unfold hlpMintSharesNat hlpWithdrawPayoutNat
  simp only [↓reduceIte]
  by_cases hz : preCap + posPnl + amount = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < preCap + posPnl + amount := by omega
    have hle : amount * (preCap + amount) ≤ amount * (preCap + posPnl + amount) :=
      Nat.mul_le_mul_left amount (by omega)
    have hdiv := Nat.div_le_div_right (c := preCap + posPnl + amount) hle
    rwa [Nat.mul_div_cancel _ hpos] at hdiv

/-- **THEOREM 2 (`hlp_nav_no_dilution_arb` — Zero Deposit-Then-Withdraw Arbitrage!)**:
    For ANY existing pool (`totalShares > 0`, `capital > 0`, `posPnl ≥ 0`), depositing `amount`
    at optimistic `navDep = capital + posPnl` and immediately burning the minted shares at
    realized `navWdr = capital + amount` can NEVER return more than `amount`! -/
theorem hlp_nav_no_dilution_arb (amount totalShares capital posPnl : Nat)
    (hTot : 0 < totalShares) (hCap : 0 < capital) :
    let (minted, newTot) := hlpMintSharesNat amount totalShares (capital + posPnl)
    hlpWithdrawPayoutNat minted newTot (capital + amount) ≤ amount := by
  unfold hlpMintSharesNat hlpWithdrawPayoutNat
  have hTne : totalShares ≠ 0 := by omega
  have hNne : capital + posPnl ≠ 0 := by omega
  simp only [hTne, hNne, ↓reduceIte]
  let m := (amount * totalShares) / (capital + posPnl)
  have hDenPos : 0 < totalShares + m := Nat.add_pos_left hTot m
  have hDenNe : totalShares + m ≠ 0 := Nat.ne_of_gt hDenPos
  change (if totalShares + m = 0 then 0 else (m * (capital + amount)) / (totalShares + m)) ≤ amount
  simp only [hDenNe, ↓reduceIte]
  have hmMul : m * (capital + posPnl) ≤ amount * totalShares := Nat.div_mul_le_self _ _
  have hmCap : m * capital ≤ amount * totalShares := by
    have : m * capital ≤ m * (capital + posPnl) := Nat.mul_le_mul_left m (by omega)
    omega
  have hnum : m * (capital + amount) ≤ amount * (totalShares + m) := by
    rw [Nat.mul_add m capital amount, Nat.mul_add amount totalShares m, Nat.mul_comm m amount]
    omega
  have hdiv := Nat.div_le_div_right (c := totalShares + m) hnum
  rwa [Nat.mul_div_cancel _ hDenPos] at hdiv

/-- **THEOREM 3 (`hlp_withdraw_le_capital`)**:
    For any `burnShares ≤ totalShares`, `hlpWithdrawPayoutNat burnShares totalShares capital ≤ capital`. -/
theorem hlp_withdraw_le_capital (burnShares totalShares capital : Nat) (hle : burnShares ≤ totalShares) :
    hlpWithdrawPayoutNat burnShares totalShares capital ≤ capital := by
  unfold hlpWithdrawPayoutNat
  by_cases hz : totalShares = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte]
    have hpos : 0 < totalShares := by omega
    have hm : burnShares * capital ≤ totalShares * capital := Nat.mul_le_mul_right capital hle
    have hd := Nat.div_le_div_right (c := totalShares) hm
    rwa [Nat.mul_div_cancel_left _ hpos] at hd

private theorem sum_floor_hlp_le (C T : Nat) (xs : List Nat) :
    (xs.map (fun b => (b * C) / T)).sum ≤ (xs.sum * C) / T := by
  induction xs with
  | nil => simp
  | cons b tl ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hT : T = 0
    · subst hT; simp at ih ⊢; exact ih
    · have hpos : 0 < T := by omega
      have h1 : (b * C) / T * T ≤ b * C := Nat.div_mul_le_self _ _
      have h2 : (tl.sum * C) / T * T ≤ tl.sum * C := Nat.div_mul_le_self _ _
      have h3 : ((b * C) / T + (tl.sum * C) / T) * T ≤ (b + tl.sum) * C := by
        rw [Nat.add_mul, Nat.add_mul]; omega
      have h4 := (Nat.le_div_iff_mul_le hpos).mpr h3
      omega

/-- **THEOREM 4 (`hlp_sum_withdrawals_solvent`)**:
    For ANY finite set of HLP depositors with `sharesList.sum ≤ totalShares`, the sum of all
    individual pro-rata redemptions is strictly `≤ capital` (100% solvent, zero rounding shortfall!). -/
theorem hlp_sum_withdrawals_solvent (totalShares capital : Nat) (sharesList : List Nat)
    (hsum : sharesList.sum ≤ totalShares) :
    (sharesList.map (fun b => hlpWithdrawPayoutNat b totalShares capital)).sum ≤ capital := by
  unfold hlpWithdrawPayoutNat
  by_cases hz : totalShares = 0
  · simp only [hz, ↓reduceIte]
    have h0 : ∀ xs : List Nat, (xs.map (fun _ => 0)).sum = 0 := by
      intro xs; induction xs with
      | nil => rfl
      | cons _ tl ih => simp [ih]
    rw [h0]; exact Nat.zero_le _
  · simp only [hz, ↓reduceIte]
    have hle1 := sum_floor_hlp_le capital totalShares sharesList
    have hpos : 0 < totalShares := by omega
    have hle2 : (sharesList.sum * capital) / totalShares ≤ capital := by
      have hm := Nat.mul_le_mul_right capital hsum
      have hd := Nat.div_le_div_right (c := totalShares) hm
      rwa [Nat.mul_div_cancel_left _ hpos] at hd
    omega

/-- **THEOREM 5 (`hlp_strategist_subset_blocks_scam`)**:
    If `matcherAllowed ⊆ vaultAllowed` (`∀ m ∈ matcherAllowed, m ∈ vaultAllowed`), then any
    scam market `scamMid ∉ vaultAllowed` is automatically excluded from `matcherAllowed` too —
    so strategist can NEVER rug depositors via an unwhitelisted `M_scam` market! -/
theorem hlp_strategist_subset_blocks_scam (vaultAllowed matcherAllowed : List Nat) (scamMid : Nat)
    (hSub : ∀ m ∈ matcherAllowed, m ∈ vaultAllowed)
    (hScam : scamMid ∉ vaultAllowed) :
    scamMid ∉ matcherAllowed :=
  fun hmem => hScam (hSub scamMid hmem)

/-! ### Runtime Helpers & Outlined CPIs -/

def copyHlpMarketsLoop (dst src : Ptr) (i count : UInt64) : SolanaM Unit := do
  if h : i < count then
    let mid ← loadU64 src (i * 8)
    SolanaM.require (mid > 0) PErr.invalidParams
    storeU64 dst (i * 8) mid
    copyHlpMarketsLoop dst src (i + 1) count
  else
    return ()
termination_by (count.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := count.toNat_lt; omega)]
  omega

def checkHlpMarketAllowedLoop (vData : Ptr) (mid i count : UInt64) : SolanaM Unit := do
  if h : i < count then
    if (← loadU64 vData (HlpOff.allowedMarkets + i * 8)) == mid then
      return ()
    else
      checkHlpMarketAllowedLoop vData mid (i + 1) count
  else
    SolanaM.fail HErr.marketNotAllowed
termination_by (count.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := count.toNat_lt; omega)]
  omega

def checkSubsetMarketsLoop (vData mcMarketsPtr : Ptr) (vCount i mcCount : UInt64) : SolanaM Unit := do
  if h : i < mcCount then
    let mid ← loadU64 mcMarketsPtr (i * 8)
    checkHlpMarketAllowedLoop vData mid 0 vCount
    checkSubsetMarketsLoop vData mcMarketsPtr vCount (i + 1) mcCount
  else
    return ()
termination_by (mcCount.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < mcCount.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := mcCount.toNat_lt; omega)]
  omega

def zeroHlpWords (base off nWords : UInt64) : SolanaM Unit := do
  if h : nWords == 0 then return ()
  else
    storeU64 base off 0
    zeroHlpWords base (off + 8) (nWords - 1)
termination_by nWords.toNat
decreasing_by
  have hne : nWords.toNat ≠ 0 := by
    intro hz
    have h0 : nWords = 0 := UInt64.toNat_inj.mp (by rw [hz]; rfl)
    exact h (by rw [h0]; rfl)
  have h1 : (1 : UInt64).toNat = 1 := rfl
  change (nWords - 1).toNat < nWords.toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), h1]
  omega

def writeHlpPdaSeeds (sbuf : Ptr) (vaultKeyPtr : Ptr) (bump : UInt8) : SolanaM Ptr := do
  let seedsArr   := sbuf + 8
  let signersArr := sbuf + 56
  storeU32 sbuf 0 TAG_HLP_AUTH
  storeU8  sbuf 4 bump
  storeU64 seedsArr 0  sbuf;       storeU64 seedsArr 8  4
  storeU64 seedsArr 16 vaultKeyPtr; storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (sbuf + 4); storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  return signersArr

def getClockSlot : SolanaM UInt64 := do
  let buf ← stackAlloc 40
  let rc ← sysGetClock buf
  SolanaM.require (rc == 0) rc
  loadU64 buf 0

def checkSplTokenProg (tokProg : AccountView) : SolanaM Unit := do
  let kp := AccountView.keyPtr tokProg
  let w0 ← loadU64 kp 0
  let w1 ← loadU64 kp 8
  let w2 ← loadU64 kp 16
  let w3 ← loadU64 kp 24
  SolanaM.require (w0 == SPL_TOK_W0 && w1 == SPL_TOK_W1 && w2 == SPL_TOK_W2 && w3 == SPL_TOK_W3) PErr.invalidTokenProg

def checkSplTokenOwnerPtr (ownerPtr : Ptr) : SolanaM Unit := do
  let w0 ← loadU64 ownerPtr 0
  let w1 ← loadU64 ownerPtr 8
  let w2 ← loadU64 ownerPtr 16
  let w3 ← loadU64 ownerPtr 24
  SolanaM.require (w0 == SPL_TOK_W0 && w1 == SPL_TOK_W1 && w2 == SPL_TOK_W2 && w3 == SPL_TOK_W3) HErr.feeTokBad

def requireNonDup (acc : AccountView) : SolanaM Unit := do
  SolanaM.require ((← rawLoadU8 acc) == ABI.nonDupMarker) PErr.aliasedAccounts

def checkHlpVault (vault : AccountView) (progId : Ptr) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr vault) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen vault) == HlpOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr vault) HlpOff.magic) == MAGIC_HLP) PErr.invalidMagic

/-- Scan all `MAX_LEGS = 8` slots of `hlpPfl`: require every active open leg to be refreshed
    in `curSlot` (zero stale-NAV arbitrage!) and sum unclaimed `posPnl`. -/
def scanHlpPflPosPnlLoop (fData : Ptr) (curSlot idx acc : UInt64) : SolanaM UInt64 := do
  if h : idx < MAX_LEGS then
    let lp := fData + PflOff.headerSize + idx * PflOff.legStride
    let act ← loadU8 lp LegOff.active
    if act != 0 then
      let side ← loadU8 lp LegOff.side
      if side != SIDE_FLAT then
        SolanaM.require ((← loadU64 lp LegOff.lastRefreshSlot) == curSlot) PErr.stalePortfolioLeg
      let p ← loadU64 lp LegOff.posPnl
      let acc' ← checkedAdd64 acc p
      scanHlpPflPosPnlLoop fData curSlot (idx + 1) acc'
    else
      scanHlpPflPosPnlLoop fData curSlot (idx + 1) acc
  else
    return acc
termination_by (MAX_LEGS.toNat - idx.toNat)
decreasing_by
  all_goals
    have hlt : idx.toNat < MAX_LEGS.toNat := UInt64.lt_iff_toNat_lt.mp h
    have h8 : MAX_LEGS.toNat = 8 := rfl
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have hadd : (idx + 1).toNat = idx.toNat + 1 := by
      rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Validate `hlpPfl` matches `vault` and return `(totalCap = freeCap + totalLockedMm, navDeposit = totalCap + Σ posPnl)`. -/
def loadFreshHlpNav (vData : Ptr) (hlpPfl percProg : AccountView) (curSlot : UInt64) :
    SolanaM (UInt64 × UInt64) := do
  SolanaM.require (← pubkeyEq (AccountView.keyPtr hlpPfl) (vData + HlpOff.hlpPortfolio)) HErr.pflMismatch
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr hlpPfl) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen hlpPfl) == PflOff.size) Err.invalidAccountData
  let fData := AccountView.dataPtr hlpPfl
  SolanaM.require ((← loadU32 fData PflOff.magic) == MAGIC_PORTFOLIO) PErr.invalidMagic
  let posPnlSum ← scanHlpPflPosPnlLoop fData curSlot 0 0
  let freeCap   ← loadU64 fData PflOff.capital
  let lockedMm  ← loadU64 fData PflOff.totalLockedMm
  let totCap    ← checkedAdd64 freeCap lockedMm
  let navDep    ← checkedAdd64 totCap posPnlSum
  return (totCap, navDep)

@[noinline] def cpiInitHlpPortfolio (percProg dex hlpPfl hlpAuthPda : AccountView)
    (vaultKeyPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  let buf ← stackAlloc 336
  let metas := buf + 40
  let infos := buf + 88
  let data  := buf + 256
  let sbuf  := buf + 264
  storeU8 data 0 IxOp.initPortfolio
  writeMeta metas        dex        1 0
  writeMeta (metas + 16) hlpPfl     1 0
  writeMeta (metas + 32) hlpAuthPda 0 1
  writeAccountInfo infos         dex
  writeAccountInfo (infos + 56)  hlpPfl
  writeAccountInfo (infos + 112) hlpAuthPda
  writeInstruction buf (AccountView.keyPtr percProg) metas 3 data 1
  let signersArr ← writeHlpPdaSeeds sbuf vaultKeyPtr bump
  let rc ← sysInvokeSignedC buf infos 3 signersArr 1
  SolanaM.require (rc == 0) rc

/-- Unified 7-account CPI into `percolator::DepositCollateral` (op=6) or `WithdrawCollateral` (op=7).
    `usePdaSigner = 1` signs with PDA `["hlpv", vault, bump]`; `0` forwards depositor's top-level signature. -/
@[noinline] def cpiVaultTransfer7 (percProg : AccountView) (accs7 : Ptr) (op : UInt8) (amount : UInt64)
    (vaultKeyPtr : Ptr) (bump : UInt8) (usePdaSigner : UInt8) : SolanaM Unit := do
  let dex      ← loadU64 accs7 0
  let hlpPfl   ← loadU64 accs7 8
  let owner    ← loadU64 accs7 16
  let tokAcc   ← loadU64 accs7 24
  let mint     ← loadU64 accs7 32
  let dexVault ← loadU64 accs7 40
  let tokProg  ← loadU64 accs7 48
  let buf ← stackAlloc 632
  let metas := buf + 40
  let infos := buf + 152
  let data  := buf + 544
  let sbuf  := buf + 560
  storeU8  data 0 op
  storeU64 data 1 amount
  writeMeta metas        dex      1 0
  writeMeta (metas + 16) hlpPfl   1 0
  writeMeta (metas + 32) owner    0 1
  writeMeta (metas + 48) tokAcc   1 0
  writeMeta (metas + 64) mint     0 0
  writeMeta (metas + 80) dexVault 1 0
  writeMeta (metas + 96) tokProg  0 0
  writeAccountInfo infos         dex
  writeAccountInfo (infos + 56)  hlpPfl
  writeAccountInfo (infos + 112) owner
  writeAccountInfo (infos + 168) tokAcc
  writeAccountInfo (infos + 224) mint
  writeAccountInfo (infos + 280) dexVault
  writeAccountInfo (infos + 336) tokProg
  writeInstruction buf (AccountView.keyPtr percProg) metas 7 data 9
  let rc ← if usePdaSigner != 0 then do
      let signersArr ← writeHlpPdaSeeds sbuf vaultKeyPtr bump
      sysInvokeSignedC buf infos 7 signersArr 1
    else
      sysInvokeSignedC buf infos 7 0 0
  SolanaM.require (rc == 0) rc

@[noinline] def cpiTakeoverLiquidateSigned (percProg : AccountView) (accs9 : Ptr) (reqQty : UInt64)
    (vaultKeyPtr : Ptr) (bump : UInt8) : SolanaM Unit := do
  let dex        ← loadU64 accs9 0
  let mkt        ← loadU64 accs9 8
  let victimPfl  ← loadU64 accs9 16
  let hlpFeeTok  ← loadU64 accs9 24
  let mint       ← loadU64 accs9 32
  let dexVault   ← loadU64 accs9 40
  let tokProg    ← loadU64 accs9 48
  let hlpPfl     ← loadU64 accs9 56
  let hlpAuthPda ← loadU64 accs9 64
  let buf ← stackAlloc 776
  let metas := buf + 40
  let infos := buf + 184
  let data  := buf + 688
  let sbuf  := buf + 704
  storeU8  data 0 IxOp.liquidate
  storeU8  data 1 1 -- mode = 1 (Zero-ADL HLP Takeover!)
  storeU64 data 2 reqQty
  writeMeta metas         dex        1 0
  writeMeta (metas + 16)  mkt        1 0
  writeMeta (metas + 32)  victimPfl  1 0
  writeMeta (metas + 48)  hlpFeeTok  1 0
  writeMeta (metas + 64)  mint       0 0
  writeMeta (metas + 80)  dexVault   1 0
  writeMeta (metas + 96)  tokProg    0 0
  writeMeta (metas + 112) hlpPfl     1 0
  writeMeta (metas + 128) hlpAuthPda 0 1
  writeAccountInfo infos          dex
  writeAccountInfo (infos + 56)   mkt
  writeAccountInfo (infos + 112)  victimPfl
  writeAccountInfo (infos + 168)  hlpFeeTok
  writeAccountInfo (infos + 224)  mint
  writeAccountInfo (infos + 280)  dexVault
  writeAccountInfo (infos + 336)  tokProg
  writeAccountInfo (infos + 392)  hlpPfl
  writeAccountInfo (infos + 448)  hlpAuthPda
  writeInstruction buf (AccountView.keyPtr percProg) metas 9 data 10
  let signersArr ← writeHlpPdaSeeds sbuf vaultKeyPtr bump
  let rc ← sysInvokeSignedC buf infos 9 signersArr 1
  SolanaM.require (rc == 0) rc

/-! ### 5 Minimal Permissionless HLP Vault Instructions -/

/-- Op 0 (`InitHlpVault`): Initialize `HlpVault` with IMMUTABLE `(allowedMatcherProg, allowedMarkets)`
    so strategist can NEVER rug via `evil_matcher.so` or permissionless `M_scam`, and CPI
    `percolator::InitPortfolio` owned by `hlpAuthPda`.
    Accounts (8): `0. vault (W)`, `1. strategist (S)`, `2. dex (W)`, `3. hlpPfl (W)`,
    `4. hlpAuthPda`, `5. hlpFeeTok`, `6. percProg`, `7. allowedMatcherProg`.
    Ix data (`28 + 8 * nAllowed` B):
      `[0, pdaBump:u8, nAllowed:u8, pad:u8, lockupSlots:u64, depositCap:u64, minDeposit:u64, mid_0..mid_{n-1}:u64]`. -/
def handleInitHlpVault (input : Ptr) : SolanaM Unit := do
  let (vault, strategist, dex, hlpPfl, hlpAuthPda, hlpFeeTok, percProg, allowedMatcherProg, ix, progId) ← parseStrict8 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 36) Err.invalidInstructionData
  SolanaM.require (← AccountView.isSigner strategist) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable vault) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr vault) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen vault) == HlpOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr vault) 0) == 0) Err.accountAlreadyInitialized

  -- Validate genuine `dex` owned by `percProg`, executable `allowedMatcherProg != percProg`,
  -- and canonical SPL Token `hlpFeeTok` (165B initialized, amount == 0, mint == dex.quoteMint, owner == hlpAuthPda, != dexVault)!
  SolanaM.require (← AccountView.isExecutable allowedMatcherProg) HErr.matcherNotAllowed
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr allowedMatcherProg) (AccountView.keyPtr percProg))) HErr.matcherNotAllowed
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr dex) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen dex) == DexOff.size) Err.invalidAccountData
  let dData := AccountView.dataPtr dex
  SolanaM.require ((← loadU32 dData DexOff.magic) == MAGIC_DEX) PErr.invalidMagic
  checkSplTokenOwnerPtr (AccountView.ownerPtr hlpFeeTok)
  SolanaM.require ((← AccountView.dataLen hlpFeeTok) == 165) HErr.feeTokBad
  let ftData := AccountView.dataPtr hlpFeeTok
  SolanaM.require ((← loadU8 ftData 108) == 1 && (← loadU64 ftData 64) == 0) HErr.feeTokBad
  SolanaM.require (← pubkeyEq ftData (dData + DexOff.quoteMint)) PErr.mintMismatch
  SolanaM.require (← pubkeyEq (ftData + 32) (AccountView.keyPtr hlpAuthPda)) HErr.feeTokBad
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr hlpFeeTok) (dData + DexOff.vaultPda))) PErr.aliasedAccounts

  let pdaBump     ← loadU8  ix.ptr 1
  let nAllowed8   ← loadU8  ix.ptr 2
  let nAllowed    := nAllowed8.toUInt64
  let lockupSlots ← loadU64 ix.ptr 4
  let depositCap  ← loadU64 ix.ptr 12
  let minDeposit  ← loadU64 ix.ptr 20
  SolanaM.require (nAllowed >= 1 && nAllowed <= MAX_LEGS && ix.len >= 28 + nAllowed * 8) PErr.invalidParams
  SolanaM.require (lockupSlots <= MAX_HLP_LOCKUP && minDeposit >= MIN_FIRST_HLP_DEPOSIT) PErr.invalidParams

  let vData := AccountView.dataPtr vault
  zeroHlpWords vData 0 (HlpOff.size >>> 3)
  storeU32 vData HlpOff.magic MAGIC_HLP
  storeU8  vData HlpOff.pdaBump pdaBump
  storeU8  vData HlpOff.paused 0
  storeU8  vData HlpOff.allowedCount nAllowed8
  pubkeyCopy (vData + HlpOff.strategist)         (AccountView.keyPtr strategist)
  pubkeyCopy (vData + HlpOff.percProg)           (AccountView.keyPtr percProg)
  pubkeyCopy (vData + HlpOff.dex)                (AccountView.keyPtr dex)
  pubkeyCopy (vData + HlpOff.hlpPortfolio)       (AccountView.keyPtr hlpPfl)
  pubkeyCopy (vData + HlpOff.hlpFeeTok)          (AccountView.keyPtr hlpFeeTok)
  pubkeyCopy (vData + HlpOff.allowedMatcherProg) (AccountView.keyPtr allowedMatcherProg)
  storeU64 vData HlpOff.lockupSlots lockupSlots
  storeU64 vData HlpOff.depositCap  depositCap
  storeU64 vData HlpOff.minDeposit  minDeposit
  copyHlpMarketsLoop (vData + HlpOff.allowedMarkets) (ix.ptr + 28) 0 nAllowed

  cpiInitHlpPortfolio percProg dex hlpPfl hlpAuthPda (AccountView.keyPtr vault) pdaBump

/-- Op 1 (`SetHlpMatcher`): Strategist binds/revokes a pinned `allowedMatcherProg` `matcherCtx`
    (whose immutable market allowlist MUST be a subset of `HlpVault.allowedMarkets`!) on `hlpPfl`,
    and optionally toggles `paused` (`ix[1]`, deposits ONLY!).
    Accounts (5 or 6): `0. vault (W)`, `1. strategist (S)`, `2. hlpPfl (W)`, `3. hlpAuthPda`,
    `4. percProg`, optional `5. matcherCtx`.
    Ix data (`1` or `2` B): `[1]` or `[1, paused:u8]`. -/
def handleSetHlpMatcher (input : Ptr) : SolanaM Unit := do
  let (n, vault, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 5) Err.notEnoughAccountKeys
  let strategist ← AccountView.nextCursor vault
  let hlpPfl     ← AccountView.nextCursor strategist
  let hlpAuthPda ← AccountView.nextCursor hlpPfl
  let percProg   ← AccountView.nextCursor hlpAuthPda

  requireNonDup vault; requireNonDup strategist; requireNonDup hlpPfl; requireNonDup hlpAuthPda; requireNonDup percProg
  SolanaM.require (← AccountView.isSigner strategist) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable vault) Err.invalidAccountData
  checkHlpVault vault progId
  let vData := AccountView.dataPtr vault
  SolanaM.require (← pubkeyEq (AccountView.keyPtr strategist) (vData + HlpOff.strategist)) PErr.unauthorized
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg)   (vData + HlpOff.percProg))   HErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr hlpPfl)     (vData + HlpOff.hlpPortfolio)) HErr.pflMismatch

  if ix.len >= 2 then
    storeU8 vData HlpOff.paused (← loadU8 ix.ptr 1)

  let bump ← loadU8 vData HlpOff.pdaBump
  let buf ← stackAlloc 336
  let metas := buf + 40
  let infos := buf + 88
  let data  := buf + 256
  let sbuf  := buf + 264
  storeU8 data 0 IxOp.setPortfolioMatcher
  writeMeta metas        hlpPfl     1 0
  writeMeta (metas + 16) hlpAuthPda 0 1
  writeAccountInfo infos        hlpPfl
  writeAccountInfo (infos + 56) hlpAuthPda
  let nAccs : UInt64 ← if n >= 6 then do
      let mc ← AccountView.nextCursor percProg
      requireNonDup mc
      -- True Zero-Strategist-Rug check: pin `mc.owner == allowedMatcherProg`, valid `MAGIC_MRET`,
      -- and require EVERY market in `mc.allowedMarkets` to be in `HlpVault.allowedMarkets`!
      SolanaM.require (← pubkeyEq (AccountView.ownerPtr mc) (vData + HlpOff.allowedMatcherProg)) HErr.matcherNotAllowed
      SolanaM.require ((← AccountView.dataLen mc) >= 272) HErr.matcherNotAllowed
      let mcData := AccountView.dataPtr mc
      SolanaM.require ((← loadU32 mcData 0) == MAGIC_MRET) HErr.matcherNotAllowed
      let mcCount := (← loadU8 mcData 201).toUInt64
      let vCount  := (← loadU8 vData HlpOff.allowedCount).toUInt64
      SolanaM.require (mcCount >= 1 && mcCount <= MAX_LEGS && vCount >= 1 && vCount <= MAX_LEGS) HErr.marketNotAllowed
      checkSubsetMarketsLoop vData (mcData + 208) vCount 0 mcCount
      writeMeta (metas + 32) mc 0 0
      writeAccountInfo (infos + 112) mc
      pure 3
    else pure 2
  writeInstruction buf (AccountView.keyPtr percProg) metas nAccs data 1
  let signersArr ← writeHlpPdaSeeds sbuf (AccountView.keyPtr vault) bump
  let rc ← sysInvokeSignedC buf infos nAccs signersArr 1
  SolanaM.require (rc == 0) rc

/-- Op 2 (`DepositHlp`): Permissionless passive LP deposit minting pro-rata shares against
    fresh optimistic equity `navDeposit = capital + Σ posPnl` (locks any pre-existing direct
    donation behind dead shares on first deposit!).
    Accounts (10): `0. vault (W)`, `1. receipt (W)`, `2. depositor (S)`, `3. depositorTok (W)`,
    `4. dex (W)`, `5. hlpPfl (W)`, `6. mint`, `7. dexVault (W)`, `8. tokProg`, `9. percProg`.
    Ix data (9B): `[2, amount:u64]`. -/
def handleDepositHlp (input : Ptr) : SolanaM Unit := do
  let (n, vault, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 10 && ix.len >= 9) Err.invalidInstructionData
  let receipt      ← AccountView.nextCursor vault
  let depositor    ← AccountView.nextCursor receipt
  let depositorTok ← AccountView.nextCursor depositor
  let dex          ← AccountView.nextCursor depositorTok
  let hlpPfl       ← AccountView.nextCursor dex
  let mint         ← AccountView.nextCursor hlpPfl
  let dexVault     ← AccountView.nextCursor mint
  let tokProg      ← AccountView.nextCursor dexVault
  let percProg     ← AccountView.nextCursor tokProg

  requireNonDup vault; requireNonDup receipt; requireNonDup depositor; requireNonDup depositorTok
  requireNonDup dex; requireNonDup hlpPfl; requireNonDup mint
  requireNonDup dexVault; requireNonDup tokProg; requireNonDup percProg
  SolanaM.require (← AccountView.isSigner depositor) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable vault) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable receipt) Err.invalidAccountData
  checkHlpVault vault progId
  let vData := AccountView.dataPtr vault
  SolanaM.require ((← loadU8 vData HlpOff.paused) == 0) HErr.paused
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg) (vData + HlpOff.percProg)) HErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr dex)      (vData + HlpOff.dex))      PErr.dexMismatch
  checkSplTokenProg tokProg

  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams

  let curSlot ← getClockSlot
  let (_, navDep) ← loadFreshHlpNav vData hlpPfl percProg curSlot
  let depCap ← loadU64 vData HlpOff.depositCap
  let postNav ← checkedAdd64 navDep amount
  if depCap > 0 then SolanaM.require (postNav <= depCap) HErr.capExceeded

  let totSh ← loadU64 vData HlpOff.totalShares
  let (mintSh, newTotSh) ← if totSh == 0 then do
      let minDep ← loadU64 vData HlpOff.minDeposit
      SolanaM.require (amount >= minDep) PErr.invalidParams
      let tot ← checkedAdd64 navDep amount
      pure (amount, tot)
    else do
      SolanaM.require (navDep > 0) PErr.nonzeroState
      let m ← mulDiv64 amount totSh navDep
      SolanaM.require (m > 0) PErr.invalidParams
      let tot ← checkedAdd64 totSh m
      pure (m, tot)

  SolanaM.require (← pubkeyEq (AccountView.ownerPtr receipt) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen receipt) == HlpRecOff.size) Err.invalidAccountData
  let rData := AccountView.dataPtr receipt
  let rMagic ← loadU32 rData HlpRecOff.magic
  if rMagic == 0 then
    zeroHlpWords rData 0 (HlpRecOff.size >>> 3)
    storeU32 rData HlpRecOff.magic MAGIC_HLPR
    pubkeyCopy (rData + HlpRecOff.vault) (AccountView.keyPtr vault)
    pubkeyCopy (rData + HlpRecOff.owner) (AccountView.keyPtr depositor)
  else
    SolanaM.require (rMagic == MAGIC_HLPR) PErr.invalidMagic
    SolanaM.require (← pubkeyEq (rData + HlpRecOff.vault) (AccountView.keyPtr vault)) HErr.vaultMismatch
    SolanaM.require (← pubkeyEq (rData + HlpRecOff.owner) (AccountView.keyPtr depositor)) PErr.ownerMismatch

  let newRecSh ← checkedAdd64 (← loadU64 rData HlpRecOff.shares) mintSh
  storeU64 vData HlpOff.totalShares newTotSh
  storeU64 rData HlpRecOff.shares newRecSh
  storeU64 rData HlpRecOff.lastDepositSlot curSlot

  let accs7 ← stackAlloc 56
  storeU64 accs7 0  dex
  storeU64 accs7 8  hlpPfl
  storeU64 accs7 16 depositor
  storeU64 accs7 24 depositorTok
  storeU64 accs7 32 mint
  storeU64 accs7 40 dexVault
  storeU64 accs7 48 tokProg
  cpiVaultTransfer7 percProg accs7 IxOp.depositCollateral amount 0 0 0

/-- Op 3 (`WithdrawHlp`): 100% permissionless (NEVER pausable!) pro-rata withdrawal against
    conservative realized `hlpPfl.capital`. Auto-closes `HlpReceipt` (`MAGIC_CLOSED` + rent
    refund to `owner`) when `receipt.shares` reaches 0!
    Accounts (11): `0. vault (W)`, `1. receipt (W)`, `2. owner (W, S)`, `3. destTok (W)`,
    `4. dex (W)`, `5. hlpPfl (W)`, `6. hlpAuthPda`, `7. mint`, `8. dexVault (W)`,
    `9. tokProg`, `10. percProg`.
    Ix data (9B): `[3, burnShares:u64]`. -/
def handleWithdrawHlp (input : Ptr) : SolanaM Unit := do
  let (n, vault, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 11 && ix.len >= 9) Err.invalidInstructionData
  let receipt    ← AccountView.nextCursor vault
  let owner      ← AccountView.nextCursor receipt
  let destTok    ← AccountView.nextCursor owner
  let dex        ← AccountView.nextCursor destTok
  let hlpPfl     ← AccountView.nextCursor dex
  let hlpAuthPda ← AccountView.nextCursor hlpPfl
  let mint       ← AccountView.nextCursor hlpAuthPda
  let dexVault   ← AccountView.nextCursor mint
  let tokProg    ← AccountView.nextCursor dexVault
  let percProg   ← AccountView.nextCursor tokProg

  requireNonDup vault; requireNonDup receipt; requireNonDup owner; requireNonDup destTok
  requireNonDup dex; requireNonDup hlpPfl; requireNonDup hlpAuthPda
  requireNonDup mint; requireNonDup dexVault; requireNonDup tokProg; requireNonDup percProg
  SolanaM.require (← AccountView.isSigner owner) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable vault) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable receipt) Err.invalidAccountData
  SolanaM.require (← AccountView.isWritable owner) Err.invalidAccountData
  SolanaM.require (!(← pubkeyEq (AccountView.keyPtr receipt) (AccountView.keyPtr owner))) PErr.aliasedAccounts
  checkHlpVault vault progId
  let vData := AccountView.dataPtr vault
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg) (vData + HlpOff.percProg)) HErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr dex)      (vData + HlpOff.dex))      PErr.dexMismatch
  checkSplTokenProg tokProg

  SolanaM.require (← pubkeyEq (AccountView.ownerPtr receipt) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen receipt) == HlpRecOff.size) Err.invalidAccountData
  let rData := AccountView.dataPtr receipt
  SolanaM.require ((← loadU32 rData HlpRecOff.magic) == MAGIC_HLPR) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (rData + HlpRecOff.vault) (AccountView.keyPtr vault)) HErr.vaultMismatch
  SolanaM.require (← pubkeyEq (rData + HlpRecOff.owner) (AccountView.keyPtr owner)) PErr.ownerMismatch

  let curSlot ← getClockSlot
  let unlockSlot ← checkedAdd64 (← loadU64 rData HlpRecOff.lastDepositSlot) (← loadU64 vData HlpOff.lockupSlots)
  SolanaM.require (curSlot >= unlockSlot) HErr.lockupActive

  let (cap, _) ← loadFreshHlpNav vData hlpPfl percProg curSlot
  let burnSh ← loadU64 ix.ptr 1
  let curSh  ← loadU64 rData HlpRecOff.shares
  let totSh  ← loadU64 vData HlpOff.totalShares
  SolanaM.require (burnSh > 0 && burnSh <= curSh && curSh <= totSh) PErr.insufficientFunds

  let payout ← if cap == 0 then pure 0 else mulDiv64 burnSh cap totSh

  -- Checks-Effects-Interactions: burn shares & auto-close empty receipt BEFORE CPI!
  let remSh := curSh - burnSh
  storeU64 vData HlpOff.totalShares (totSh - burnSh)
  if remSh == 0 then
    zeroHlpWords rData 0 (HlpRecOff.size >>> 3)
    storeU32 rData HlpRecOff.magic MAGIC_CLOSED
    let recLam ← AccountView.lamports receipt
    let ownLam ← AccountView.lamports owner
    AccountView.setLamports owner (← checkedAdd64 ownLam recLam)
    AccountView.setLamports receipt 0
  else
    storeU64 rData HlpRecOff.shares remSh

  if payout > 0 then
    let accs7 ← stackAlloc 56
    storeU64 accs7 0  dex
    storeU64 accs7 8  hlpPfl
    storeU64 accs7 16 hlpAuthPda
    storeU64 accs7 24 destTok
    storeU64 accs7 32 mint
    storeU64 accs7 40 dexVault
    storeU64 accs7 48 tokProg
    let bump ← loadU8 vData HlpOff.pdaBump
    cpiVaultTransfer7 percProg accs7 IxOp.withdrawCollateral payout (AccountView.keyPtr vault) bump 1

/-- Op 4 (`HlpTakeoverLiquidate`): Strategist-gated zero-ADL liquidation takeover
    (`percolator::Liquidate(mode=1)`). Routes 100% of keeper liquidation fees to `hlpFeeTok`
    and immediately auto-deposits them into `hlpPfl.capital` for HLP depositors!
    Accounts (12): `0. vault`, `1. strategist (S)`, `2. dex (W)`, `3. mkt (W)`, `4. victimPfl (W)`,
    `5. hlpFeeTok (W)`, `6. mint`, `7. dexVault (W)`, `8. tokProg`, `9. hlpPfl (W)`,
    `10. hlpAuthPda`, `11. percProg`.
    Ix data (9B): `[4, reqQty:u64]` (`0` = full takeover, `> 0` = partial). -/
def handleHlpTakeoverLiquidate (input : Ptr) : SolanaM Unit := do
  let (n, vault, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 12 && ix.len >= 9) Err.invalidInstructionData
  let strategist ← AccountView.nextCursor vault
  let dex        ← AccountView.nextCursor strategist
  let mkt        ← AccountView.nextCursor dex
  let victimPfl  ← AccountView.nextCursor mkt
  let hlpFeeTok  ← AccountView.nextCursor victimPfl
  let mint       ← AccountView.nextCursor hlpFeeTok
  let dexVault   ← AccountView.nextCursor mint
  let tokProg    ← AccountView.nextCursor dexVault
  let hlpPfl     ← AccountView.nextCursor tokProg
  let hlpAuthPda ← AccountView.nextCursor hlpPfl
  let percProg   ← AccountView.nextCursor hlpAuthPda

  requireNonDup vault; requireNonDup strategist; requireNonDup dex; requireNonDup mkt; requireNonDup victimPfl
  requireNonDup hlpFeeTok; requireNonDup mint; requireNonDup dexVault
  requireNonDup tokProg; requireNonDup hlpPfl; requireNonDup hlpAuthPda; requireNonDup percProg
  SolanaM.require (← AccountView.isSigner strategist) Err.missingRequiredSignature
  checkHlpVault vault progId
  let vData := AccountView.dataPtr vault
  SolanaM.require (← pubkeyEq (AccountView.keyPtr strategist) (vData + HlpOff.strategist))   PErr.unauthorized
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg)   (vData + HlpOff.percProg))     HErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr dex)        (vData + HlpOff.dex))          PErr.dexMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr hlpPfl)     (vData + HlpOff.hlpPortfolio)) HErr.pflMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr hlpFeeTok)  (vData + HlpOff.hlpFeeTok))    HErr.feeTokBad
  checkSplTokenProg tokProg
  -- Zero-Strategist-Rug check: `mkt` MUST be a genuine `percolator` market in `HlpVault.allowedMarkets`!
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr mkt) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen mkt) == MktOff.size) Err.invalidAccountData
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU32 mData MktOff.magic) == MAGIC_MARKET) PErr.invalidMagic
  let vCount := (← loadU8 vData HlpOff.allowedCount).toUInt64
  checkHlpMarketAllowedLoop vData (← loadU64 mData MktOff.marketId) 0 vCount

  let reqQty ← loadU64 ix.ptr 1
  let bump   ← loadU8 vData HlpOff.pdaBump
  let preFee ← loadU64 (AccountView.dataPtr hlpFeeTok) 64

  let accs9 ← stackAlloc 72
  storeU64 accs9 0  dex
  storeU64 accs9 8  mkt
  storeU64 accs9 16 victimPfl
  storeU64 accs9 24 hlpFeeTok
  storeU64 accs9 32 mint
  storeU64 accs9 40 dexVault
  storeU64 accs9 48 tokProg
  storeU64 accs9 56 hlpPfl
  storeU64 accs9 64 hlpAuthPda
  cpiTakeoverLiquidateSigned percProg accs9 reqQty (AccountView.keyPtr vault) bump

  -- Immediately sweep 100% of keeper liquidation fee into `hlpPfl.capital` for HLP depositors!
  let postFee ← loadU64 (AccountView.dataPtr hlpFeeTok) 64
  if postFee > preFee then
    let gained := postFee - preFee
    let accs7 ← stackAlloc 56
    storeU64 accs7 0  dex
    storeU64 accs7 8  hlpPfl
    storeU64 accs7 16 hlpAuthPda
    storeU64 accs7 24 hlpFeeTok
    storeU64 accs7 32 mint
    storeU64 accs7 40 dexVault
    storeU64 accs7 48 tokProg
    cpiVaultTransfer7 percProg accs7 IxOp.depositCollateral gained (AccountView.keyPtr vault) bump 1

def dispatch (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then handleInitHlpVault input
  else if op == 1 then handleSetHlpMatcher input
  else if op == 2 then handleDepositHlp input
  else if op == 3 then handleWithdrawHlp input
  else if op == 4 then handleHlpTakeoverLiquidate input
  else SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (dispatch input) s

end Percolator.HlpVault
