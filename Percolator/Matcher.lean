/-
  Percolator.Matcher
  Minimal, formally verified 0-Signer Multi-Market CPI-Out PropAMM reference program for
  `percolator-lean::TradeWithMatcher`.

  Zero custody, zero PDA signer delegation, zero transaction introspection:
  - LP retains 100% EOA ownership over their `percolator` `Portfolio` and binds `PropCtx`
    via `SetPortfolioMatcher`.
  - `TradeWithMatcher` passes ALL `k ∈ [1..8]` offers in ONE single 0-signer CPI (`Op 2`),
    so the PropAMM sees the full basket atomically: if a multi-market batch contains BOTH
    buying and selling legs (`mask == 3`), it grants a 50% hedged-basket half-spread discount!
  - Standard market pricing on BOTH open (`mode = 0`) and reduce (`mode = 1`):
    buyers (`open Long` / `reduce Short`) always receive Ask (`≥ markP`),
    sellers (`open Short` / `reduce Long`) always receive Bid (`≤ markP`).
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.Matcher

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open Percolator

namespace MErr
  def paused           : UInt64 := 200
  def marketNotAllowed : UInt64 := 201
end MErr

/-! Zero-copy Multi-Market CPI-Out PropAMM Context (`272` bytes):
    Bytes `0..144` hold the standard `percolator` `MatcherReturn` header (`16 B`: `[magic="MRET", status, seq]`)
    followed by up to `MAX_LEGS = 8` × `16 B` `(execPrice_i, fillQty_i)` quote slots (`16..144`).
    Bytes `144..208` hold mutable quoting params (`owner`, `halfSpreadBps`, `impactBps`, `maxFillQty`, `paused`).
    Bytes `201` + `208..272` hold the IMMUTABLE market allowlist (`allowedCount:u8`, `allowedMarkets:[u64;8]`)
    so no anonymous attacker (nor HLP strategist!) can ever force this LP onto a permissionless scam market! -/
namespace PropOff
  def size           : UInt64 := 272
  def magic          : UInt64 := 0   -- u32 ("MRET")
  def status         : UInt64 := 4   -- u32 (0 = ok)
  def seq            : UInt64 := 8   -- u64
  def quotesBase     : UInt64 := 16  -- 8 × 16B `(execPrice:u64, fillQty:u64)`
  def owner          : UInt64 := 144 -- Pubkey (32)
  def halfSpreadBps  : UInt64 := 176 -- u64
  def impactBps      : UInt64 := 184 -- u64
  def maxFillQty     : UInt64 := 192 -- u64
  def paused         : UInt64 := 200 -- u8
  def allowedCount   : UInt64 := 201 -- u8 (1..8, IMMUTABLE after InitPropAmm!)
  def allowedMarkets : UInt64 := 208 -- 8 × u64 (IMMUTABLE pinned marketId allowlist!)
end PropOff

theorem matcher_layout_sizes_valid :
    PropOff.quotesBase + MAX_LEGS * 16 ≤ PropOff.owner ∧
    PropOff.allowedMarkets + MAX_LEGS * 8 ≤ PropOff.size ∧ PropOff.size % 8 == 0 := by
  decide

/-! ### Pure Quote Specification & Formal Proofs (0 `sorry`, 0 custom axioms) -/

def clampSpreadBpsNat (halfSpread impact qty maxMove : Nat) : Nat :=
  min (halfSpread + (qty * impact) / 1_000_000) maxMove

def quoteAskNat (markP halfSpread impact qty maxMove : Nat) : Nat :=
  markP + (markP * clampSpreadBpsNat halfSpread impact qty maxMove) / 10_000

def quoteBidNat (markP halfSpread impact qty maxMove : Nat) : Nat :=
  let delta := (markP * clampSpreadBpsNat halfSpread impact qty maxMove) / 10_000
  if markP > delta then markP - delta else 1

theorem quoteAsk_ge_mark (markP halfSpread impact qty maxMove : Nat) :
    quoteAskNat markP halfSpread impact qty maxMove ≥ markP := by
  unfold quoteAskNat; omega

theorem quoteBid_le_mark (markP halfSpread impact qty maxMove : Nat) (hm : markP ≥ 1) :
    quoteBidNat markP halfSpread impact qty maxMove ≤ markP := by
  unfold quoteBidNat; dsimp only; split <;> omega

theorem quoteAsk_within_maxMove (markP halfSpread impact qty maxMove : Nat) :
    quoteAskNat markP halfSpread impact qty maxMove - markP ≤ (markP * maxMove) / 10_000 := by
  unfold quoteAskNat clampSpreadBpsNat
  have hle : min (halfSpread + (qty * impact) / 1_000_000) maxMove ≤ maxMove := Nat.min_le_right _ _
  have hmul : markP * min (halfSpread + (qty * impact) / 1_000_000) maxMove ≤ markP * maxMove :=
    Nat.mul_le_mul_left markP hle
  have hdiv := Nat.div_le_div_right (c := 10_000) hmul
  omega

theorem quoteBid_within_maxMove (markP halfSpread impact qty maxMove : Nat) (hm : markP ≥ 1) :
    markP - quoteBidNat markP halfSpread impact qty maxMove ≤ (markP * maxMove) / 10_000 := by
  unfold quoteBidNat clampSpreadBpsNat; dsimp only
  have hle : min (halfSpread + (qty * impact) / 1_000_000) maxMove ≤ maxMove := Nat.min_le_right _ _
  have hmul : markP * min (halfSpread + (qty * impact) / 1_000_000) maxMove ≤ markP * maxMove :=
    Nat.mul_le_mul_left markP hle
  have hdiv := Nat.div_le_div_right (c := 10_000) hmul
  split <;> omega

/-- Formal Proof #5 (`PropAMM` Universal Open/Reduce/Flip Spread-Direction Soundness):
    Across ALL allowed modes (`mode = 0` open, `mode = 1` reduce, `mode = 4` auto-netted flip),
    computing `takerIsBuying = (mode != 1 && takerIsLong) || (mode == 1 && !takerIsLong)` quotes:
    - Ask (`≥ markP`) whenever taker is buying (`open Long`, `reduce Short`, or `netted Buy/Flip`),
    - Bid (`≤ markP`) whenever taker is selling (`open Short`, `reduce Long`, or `netted Sell/Flip`),
    so `tradeCore`/`tradeNettedCore` ALWAYS directs spread strictly FROM taker TO passive LP! -/
theorem matcher_fill_spread_favors_lp
    (mode : UInt8) (takerIsLong : Bool) (markP halfSpread impact qty maxMove : Nat)
    (hmode : mode = 0 ∨ mode = 1 ∨ mode = 4) (hm : markP ≥ 1) :
    let takerIsBuying := (mode != 1 && takerIsLong) || (mode == 1 && !takerIsLong)
    (mode ≠ 2 ∧ mode ≠ 3) ∧
    (if takerIsBuying then quoteAskNat markP halfSpread impact qty maxMove ≥ markP
     else quoteBidNat markP halfSpread impact qty maxMove ≤ markP) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rcases hmode with rfl | rfl | rfl <;> decide
  · rcases hmode with rfl | rfl | rfl <;> cases takerIsLong
    · exact quoteBid_le_mark markP halfSpread impact qty maxMove hm
    · exact quoteAsk_ge_mark markP halfSpread impact qty maxMove
    · exact quoteAsk_ge_mark markP halfSpread impact qty maxMove
    · exact quoteBid_le_mark markP halfSpread impact qty maxMove hm
    · exact quoteBid_le_mark markP halfSpread impact qty maxMove hm
    · exact quoteAsk_ge_mark markP halfSpread impact qty maxMove

/-- Pure allowlist predicate matching `checkMarketAllowedLoop`. -/
def isAllowedMarketNat (allowed : List Nat) (mid : Nat) : Bool :=
  allowed.any (fun m => m == mid)

/-- Formal Proof #6 (`matcher_allowlist_rejects_unlisted`):
    Any permissionless scam market `scamMid` not in the PropAMM's immutable allowlist is
    unconditionally rejected (`isAllowedMarketNat allowed scamMid = false`)! -/
theorem matcher_allowlist_rejects_unlisted (allowed : List Nat) (scamMid : Nat)
    (hNotIn : scamMid ∉ allowed) :
    isAllowedMarketNat allowed scamMid = false := by
  unfold isAllowedMarketNat
  induction allowed with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.any_cons]
    have hne : (a == scamMid) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq; exact hNotIn (heq ▸ List.mem_cons_self ..)
    rw [hne, Bool.false_or]
    exact ih (fun hmem => hNotIn (List.mem_cons_of_mem a hmem))

/-! ### Runtime Helpers & 3 Minimal CPI-Out Instructions -/

def zeroMatcherWords (base off nWords : UInt64) : SolanaM Unit := do
  if h : nWords == 0 then return ()
  else
    storeU64 base off 0
    zeroMatcherWords base (off + 8) (nWords - 1)
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

def copyAllowedMarketsLoop (dst src : Ptr) (i count : UInt64) : SolanaM Unit := do
  if h : i < count then
    let mid ← loadU64 src (i * 8)
    SolanaM.require (mid > 0) PErr.invalidParams
    storeU64 dst (i * 8) mid
    copyAllowedMarketsLoop dst src (i + 1) count
  else
    return ()
termination_by (count.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := count.toNat_lt; omega)]
  omega

def checkMarketAllowedLoop (d : Ptr) (mid i count : UInt64) : SolanaM Unit := do
  if h : i < count then
    if (← loadU64 d (PropOff.allowedMarkets + i * 8)) == mid then
      return ()
    else
      checkMarketAllowedLoop d mid (i + 1) count
  else
    SolanaM.fail MErr.marketNotAllowed
termination_by (count.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < count.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := count.toNat_lt; omega)]
  omega

/-- Op 0 (`InitPropAmm`): Initialize a 272-byte CPI-Out PropAMM context (`owner == progId`, `magic == 0`)
    with an IMMUTABLE market allowlist (`nAllowed ∈ [1..8]`).
    Accounts: `0. ctx (W)`, `1. owner (S)`.
    Ix data (`28 + 8 * nAllowed` B):
      `[0, paused:u8, nAllowed:u8, pad:u8, halfSpreadBps:u64, impactBps:u64, maxFillQty:u64, mid_0..mid_{n-1}:u64]`. -/
def handleInitPropAmm (input : Ptr) : SolanaM Unit := do
  let (ctx, owner, ix, progId) ← parseStrict2 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 36) Err.invalidInstructionData
  SolanaM.require (← AccountView.isSigner owner) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable ctx) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr ctx) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen ctx) == PropOff.size) Err.invalidAccountData
  SolanaM.require ((← loadU32 (AccountView.dataPtr ctx) 0) == 0) Err.accountAlreadyInitialized
  let paused        ← loadU8  ix.ptr 1
  let nAllowed8     ← loadU8  ix.ptr 2
  let nAllowed      := nAllowed8.toUInt64
  let halfSpreadBps ← loadU64 ix.ptr 4
  let impactBps     ← loadU64 ix.ptr 12
  let maxFillQty    ← loadU64 ix.ptr 20
  SolanaM.require (nAllowed >= 1 && nAllowed <= MAX_LEGS && ix.len >= 28 + nAllowed * 8) PErr.invalidParams
  SolanaM.require (halfSpreadBps <= BPS_DEN && maxFillQty > 0) PErr.invalidParams
  let d := AccountView.dataPtr ctx
  zeroMatcherWords d 0 (PropOff.size >>> 3)
  storeU32 d PropOff.magic MAGIC_MRET
  storeU32 d PropOff.status 0
  pubkeyCopy (d + PropOff.owner) (AccountView.keyPtr owner)
  storeU64 d PropOff.halfSpreadBps halfSpreadBps
  storeU64 d PropOff.impactBps     impactBps
  storeU64 d PropOff.maxFillQty    maxFillQty
  storeU8  d PropOff.paused        paused
  storeU8  d PropOff.allowedCount  nAllowed8
  copyAllowedMarketsLoop (d + PropOff.allowedMarkets) (ix.ptr + 28) 0 nAllowed

/-- Op 1 (`UpdatePropAmm`): Owner updates PropAMM quoting parameters or pauses quoting.
    Accounts: `0. ctx (W)`, `1. owner (S)`.
    Ix data (28B): `[1, paused:u8, pad:u16, halfSpreadBps:u64, impactBps:u64, maxFillQty:u64]`. -/
def handleUpdatePropAmm (input : Ptr) : SolanaM Unit := do
  let (ctx, owner, ix, progId) ← parseStrict2 input PErr.aliasedAccounts
  SolanaM.require (ix.len >= 28) Err.invalidInstructionData
  SolanaM.require (← AccountView.isSigner owner) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable ctx) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr ctx) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen ctx) == PropOff.size) Err.invalidAccountData
  let d := AccountView.dataPtr ctx
  SolanaM.require ((← loadU32 d PropOff.magic) == MAGIC_MRET) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.keyPtr owner) (d + PropOff.owner)) PErr.ownerMismatch
  let paused        ← loadU8  ix.ptr 1
  let halfSpreadBps ← loadU64 ix.ptr 4
  let impactBps     ← loadU64 ix.ptr 12
  let maxFillQty    ← loadU64 ix.ptr 20
  SolanaM.require (halfSpreadBps <= BPS_DEN && maxFillQty > 0) PErr.invalidParams
  storeU8  d PropOff.paused        paused
  storeU64 d PropOff.halfSpreadBps halfSpreadBps
  storeU64 d PropOff.impactBps     impactBps
  storeU64 d PropOff.maxFillQty    maxFillQty

/-- Scan all `k` offers in the CPI-Out request to return a 2-bit economic buy/sell mask:
    bit 0 = hasSell, bit 1 = hasBuy. When `(mask == 3)` (both buys & sells in ONE batch!),
    the PropAMM sees a hedged basket without tx introspection and grants a 50% spread discount! -/
def scanBatchSideMask (ixPtr : Ptr) (i k mask : UInt64) : SolanaM UInt64 := do
  if _h : i < k then
    let oPtr := ixPtr + 32 + i * 48
    let mode ← loadU8 oPtr 0
    let side ← loadU8 oPtr 1
    let isBuying := (mode != 1 && side != 0) || (mode == 1 && side == 0)
    let bit : UInt64 := if isBuying then 2 else 1
    scanBatchSideMask ixPtr (i + 1) k (mask ||| bit)
  else
    return mask
termination_by (k.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp _h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := k.toNat_lt; omega)]
  omega

/-- Quote all `k` markets in ONE CPI call, enforcing the IMMUTABLE market allowlist on every leg
    and writing `(execPrice_i, fillQty_i)` into `d[16 + i*16]`. -/
def quoteBatchOffersLoop (d ixPtr : Ptr) (effHalfSp nAllowed i k : UInt64) : SolanaM Unit := do
  if h : i < k then
    let oPtr := ixPtr + 32 + i * 48
    let mode        ← loadU8  oPtr 0
    let takerIsLong ← loadU8  oPtr 1
    let mid         ← loadU64 oPtr 8
    let maxQty      ← loadU64 oPtr 16
    let markP       ← loadU64 oPtr 32
    let maxMove     ← loadU64 oPtr 40
    SolanaM.require ((mode == 0 || mode == 1 || mode == 4) && maxQty > 0 && markP > 0) PErr.invalidParams
    checkMarketAllowedLoop d mid 0 nAllowed

    let maxFill ← loadU64 d PropOff.maxFillQty
    let fillQty := if maxQty < maxFill then maxQty else maxFill
    let impBps  ← loadU64 d PropOff.impactBps
    let imp     ← mulDiv64 fillQty impBps POS_SCALE
    let rawBps  ← checkedAdd64 effHalfSp imp
    let effBps  := if rawBps > maxMove then maxMove else rawBps
    let delta   ← mulDiv64 markP effBps BPS_DEN
    let isBuying := (mode != 1 && takerIsLong != 0) || (mode == 1 && takerIsLong == 0)
    let execPrice ← if isBuying then
        checkedAdd64 markP delta
      else
        pure (if markP > delta then markP - delta else 1)

    let qOff := PropOff.quotesBase + i * 16
    storeU64 d qOff       execPrice
    storeU64 d (qOff + 8) fillQty
    quoteBatchOffersLoop d ixPtr effHalfSp nAllowed (i + 1) k
  else
    return ()
termination_by (k.toNat - i.toNat)
decreasing_by
  have hlt : i.toNat < k.toNat := UInt64.lt_iff_toNat_lt.mp h
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, h1, Nat.mod_eq_of_lt (by have := k.toNat_lt; omega)]
  omega

/-- Op 2 (`PropAmmQuote`): Multi-Market (`k ∈ [1..8]`) CPI-Out PropAMM quoting entrypoint invoked
    by `percolator::TradeWithMatcher` with ZERO signers (`[ctx (W)]`).
    Enforces the immutable market allowlist on every leg and halves `halfSpreadBps` on hedged baskets! -/
def handlePropAmmQuote (input : Ptr) : SolanaM Unit := do
  let (n, ctx, ix, progId) ← parseIxOnly input
  SolanaM.require (n >= 1 && ix.len >= 80) Err.invalidInstructionData
  AccountView.requireNonDup ctx PErr.aliasedAccounts
  SolanaM.require (← AccountView.isWritable ctx) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr ctx) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen ctx) == PropOff.size) Err.invalidAccountData
  let d := AccountView.dataPtr ctx
  SolanaM.require ((← loadU32 d PropOff.magic) == MAGIC_MRET) PErr.invalidMagic
  SolanaM.require ((← loadU8 d PropOff.paused) == 0) MErr.paused

  let k := (← loadU8 ix.ptr 1).toUInt64
  SolanaM.require (k >= 1 && k <= MAX_LEGS && ix.len >= 32 + k * 48) Err.invalidInstructionData
  let nAllowed := (← loadU8 d PropOff.allowedCount).toUInt64
  SolanaM.require (nAllowed >= 1 && nAllowed <= MAX_LEGS) MErr.marketNotAllowed
  let reqSeq ← loadU64 ix.ptr 24

  let halfSp ← loadU64 d PropOff.halfSpreadBps
  let mask ← scanBatchSideMask ix.ptr 0 k 0
  let effHalfSp := if k >= 2 && mask == 3 then halfSp >>> 1 else halfSp

  quoteBatchOffersLoop d ix.ptr effHalfSp nAllowed 0 k
  storeU32 d PropOff.magic  MAGIC_MRET
  storeU32 d PropOff.status 0
  storeU64 d PropOff.seq    reqSeq

def dispatch (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then handleInitPropAmm input
  else if op == 1 then handleUpdatePropAmm input
  else if op == 2 then handlePropAmmQuote input
  else SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (dispatch input) s

end Percolator.Matcher
