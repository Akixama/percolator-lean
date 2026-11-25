/-
  Percolator.OracleAdapter
  Minimal, formally verified permissionless external oracle + on-chain funding bridge
  that composes with `percolator-lean` via CPI (`sol_invoke_signed_c`).

  Zero changes to core `percolator-lean`:
  - Derives PDA `["orac", adapter.key, bump]` assigned as `Market.oracleAuth`.
  - Any permissionless keeper invokes `Crank` (0 signers required!):
    1. Reads an external on-chain price feed account (`price`, `conf`, `publishSlot`).
    2. Enforces feed staleness (`curSlot - publishSlot <= maxFeedAge`) and confidence bounds.
    3. Auto-clamps the price step to `±mkt.maxMoveBps` (smooth multi-slot convergence!).
    4. Computes on-chain premium funding strictly within the remaining per-slot clamp budget.
    5. CPIs `percolator::UpdateOracle` signing with the oracle adapter PDA!
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.OracleAdapter

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open LeanSVM.CPI
open Percolator

def MAGIC_ADAPTER : UInt32 := 0x5044414F -- "OADP"
def MAGIC_FEED    : UInt32 := 0x44454546 -- "FEED"
def TAG_ORAC_AUTH : UInt32 := 0x6361726F -- "orac"

namespace OErr
  def feedStale    : UInt64 := 300
  def feedWideConf : UInt64 := 301
  def feedMismatch : UInt64 := 302
  def progMismatch : UInt64 := 303
end OErr

namespace AdpOff
  def size              : UInt64 := 192
  def magic             : UInt64 := 0   -- u32 ("OADP")
  def pdaBump           : UInt64 := 4   -- u8
  def admin             : UInt64 := 8   -- Pubkey (32)
  def percProg          : UInt64 := 40  -- Pubkey (32)
  def market            : UInt64 := 72  -- Pubkey (32)
  def feedAccount       : UInt64 := 104 -- Pubkey (32)
  def maxFeedAge        : UInt64 := 136 -- u64
  def maxConfBps        : UInt64 := 144 -- u64
  def fundingBpsPerStep : UInt64 := 152 -- u64
  def feedOwner         : UInt64 := 160 -- Pubkey (32) — pinned owner of `feedAccount`
end AdpOff

namespace FeedOff
  def size        : UInt64 := 32
  def magic       : UInt64 := 0  -- u32 ("FEED")
  def price       : UInt64 := 8  -- u64 (E6)
  def conf        : UInt64 := 16 -- u64 (E6)
  def publishSlot : UInt64 := 24 -- u64
end FeedOff

/-! ### Pure Clamped Convergence + Funding Specification & Formal Proofs -/

def clampedStepNat (oldP targetP maxMoveBps : Nat) : Nat × Nat :=
  let maxAllowed := (oldP * maxMoveBps) / 10_000
  if targetP ≥ oldP then
    let step := min (targetP - oldP) maxAllowed
    (oldP + step, step)
  else
    let step := min (oldP - targetP) maxAllowed
    if oldP > step then (oldP - step, step) else (1, oldP - 1)

def clampedFundingNat (oldP step maxMoveBps fundBps : Nat) : Nat :=
  let maxAllowed := (oldP * maxMoveBps) / 10_000
  let remBudget  := maxAllowed - step
  min ((oldP * fundBps) / 10_000) remBudget

/-- Formal Proof: `clampedStepNat` + `clampedFundingNat` ALWAYS satisfies `percolator-lean`'s
    per-slot oracle clamp `|newP - oldP| + fundE6 ≤ ⌊oldP * maxMoveBps / 10_000⌋`! -/
theorem crank_step_and_funding_within_clamp (oldP targetP maxMoveBps fundBps : Nat) (ho : oldP ≥ 1) :
    let (newP, step) := clampedStepNat oldP targetP maxMoveBps
    let fundE6 := clampedFundingNat oldP step maxMoveBps fundBps
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    diff + fundE6 ≤ (oldP * maxMoveBps) / 10_000 := by
  unfold clampedStepNat clampedFundingNat
  dsimp only
  by_cases h1 : targetP ≥ oldP
  · simp only [h1, ↓reduceIte]
    split <;> omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : oldP > min (oldP - targetP) (oldP * maxMoveBps / 10_000)
    · simp only [h2, ↓reduceIte]; split <;> omega
    · simp only [h2, ↓reduceIte]; split <;> omega

/-! ### CPI Signer Helper -/

def writeOracPdaSeeds (sbuf : Ptr) (adpKeyPtr : Ptr) (bump : UInt8) : SolanaM Ptr := do
  let seedsArr   := sbuf + 8
  let signersArr := sbuf + 56
  storeU32 sbuf 0 TAG_ORAC_AUTH
  storeU8  sbuf 4 bump
  storeU64 seedsArr 0  sbuf;       storeU64 seedsArr 8  4
  storeU64 seedsArr 16 adpKeyPtr;  storeU64 seedsArr 24 32
  storeU64 seedsArr 32 (sbuf + 4); storeU64 seedsArr 40 1
  storeU64 signersArr 0 seedsArr
  storeU64 signersArr 8 3
  return signersArr

def getSlot : SolanaM UInt64 := do
  let buf ← stackAlloc 40
  let rc ← sysGetClock buf
  SolanaM.require (rc == 0) Err.invalidAccountData
  loadU64 buf 0

/-! ### 2 Minimal Instructions -/

/-- Op 0: Initialize `OracleAdapter` binding `(percolatorProg, market, feedAccount)`. -/
def handleInitAdapter (input : Ptr) : SolanaM Unit := do
  let (adp, admin, percProg, mkt, feed, ix, progId) ← parse5 input
  SolanaM.require (ix.len >= 28) Err.invalidInstructionData
  SolanaM.require (← AccountView.isSigner admin) Err.missingRequiredSignature
  SolanaM.require (← AccountView.isWritable adp) Err.invalidAccountData
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr adp) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen adp) >= AdpOff.size) Err.accountDataTooSmall
  SolanaM.require ((← loadU32 (AccountView.dataPtr adp) 0) == 0) Err.accountAlreadyInitialized

  let pdaBump     ← loadU8  ix.ptr 1
  let maxFeedAge  ← loadU64 ix.ptr 4
  let maxConfBps  ← loadU64 ix.ptr 12
  let fundBpsStep ← loadU64 ix.ptr 20
  SolanaM.require (maxFeedAge >= 1 && maxConfBps <= BPS_DEN && fundBpsStep <= BPS_DEN) PErr.invalidParams

  let aData := AccountView.dataPtr adp
  storeU32 aData AdpOff.magic MAGIC_ADAPTER
  storeU8  aData AdpOff.pdaBump pdaBump
  pubkeyCopy (aData + AdpOff.admin)       (AccountView.keyPtr admin)
  pubkeyCopy (aData + AdpOff.percProg)    (AccountView.keyPtr percProg)
  pubkeyCopy (aData + AdpOff.market)      (AccountView.keyPtr mkt)
  pubkeyCopy (aData + AdpOff.feedAccount) (AccountView.keyPtr feed)
  pubkeyCopy (aData + AdpOff.feedOwner)   (AccountView.ownerPtr feed)
  storeU64 aData AdpOff.maxFeedAge        maxFeedAge
  storeU64 aData AdpOff.maxConfBps        maxConfBps
  storeU64 aData AdpOff.fundingBpsPerStep fundBpsStep

/-- Op 1: 100% Permissionless `Crank` — reads external feed, clamps price, computes funding,
    and CPIs `percolator::UpdateOracle` signed by the adapter's PDA! -/
def handleCrank (input : Ptr) : SolanaM Unit := do
  let (adp, mkt, feed, oracAuthPda, percProg, _, progId) ← parse5 input
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr adp) progId) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen adp) >= AdpOff.size) Err.accountDataTooSmall
  let aData := AccountView.dataPtr adp
  SolanaM.require ((← loadU32 aData AdpOff.magic) == MAGIC_ADAPTER) PErr.invalidMagic
  SolanaM.require (← pubkeyEq (AccountView.keyPtr percProg) (aData + AdpOff.percProg))    OErr.progMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr mkt)      (aData + AdpOff.market))      PErr.marketMismatch
  SolanaM.require (← pubkeyEq (AccountView.keyPtr feed)     (aData + AdpOff.feedAccount)) OErr.feedMismatch
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr feed)   (aData + AdpOff.feedOwner))   Err.illegalOwner

  -- Validate `feed` account & read price/confidence/publishSlot
  SolanaM.require ((← AccountView.dataLen feed) >= FeedOff.size) Err.accountDataTooSmall
  let fData := AccountView.dataPtr feed
  SolanaM.require ((← loadU32 fData FeedOff.magic) == MAGIC_FEED) PErr.invalidMagic
  let feedPrice ← loadU64 fData FeedOff.price
  let feedConf  ← loadU64 fData FeedOff.conf
  let pubSlot   ← loadU64 fData FeedOff.publishSlot
  SolanaM.require (feedPrice > 0 && feedPrice <= MAX_PRICE) PErr.invalidParams

  let curSlot ← getSlot
  let maxAge ← loadU64 aData AdpOff.maxFeedAge
  SolanaM.require (curSlot >= pubSlot && (curSlot - pubSlot) <= maxAge) OErr.feedStale
  let maxConf ← mulDiv64 feedPrice (← loadU64 aData AdpOff.maxConfBps) BPS_DEN
  SolanaM.require (feedConf <= maxConf) OErr.feedWideConf

  -- Read `oldPrice` & `maxMoveBps` from `percolator::Market`
  SolanaM.require (← pubkeyEq (AccountView.ownerPtr mkt) (AccountView.keyPtr percProg)) Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen mkt) >= MktOff.size) Err.accountDataTooSmall
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU32 mData MktOff.magic) == MAGIC_MARKET) PErr.invalidMagic
  let oldP ← loadU64 mData MktOff.markPrice
  let maxAllowed ← mulDiv64 oldP (← loadU64 mData MktOff.maxMoveBps) BPS_DEN

  -- Clamp price step smoothly toward `feedPrice`
  let (newP, step) : UInt64 × UInt64 :=
    if feedPrice >= oldP then
      let raw := feedPrice - oldP
      let s := if raw < maxAllowed then raw else maxAllowed
      (oldP + s, s)
    else
      let raw := oldP - feedPrice
      let s := if raw < maxAllowed then raw else maxAllowed
      if oldP > s then (oldP - s, s) else (1, oldP - 1)

  -- Compute on-chain premium funding strictly within remaining clamp budget
  let remBudget := if maxAllowed >= step then maxAllowed - step else 0
  let fundBps ← loadU64 aData AdpOff.fundingBpsPerStep
  let (fundSign, fundE6) ← if feedPrice != newP && remBudget > 0 && fundBps > 0 then do
      let rawF ← mulDiv64 oldP fundBps BPS_DEN
      let f := if rawF < remBudget then rawF else remBudget
      let sign : UInt8 := if newP > feedPrice then 0 else 1
      pure (sign, f)
    else pure (0, 0)

  -- CPI `percolator::UpdateOracle(mkt[W], oracAuthPda[S])`
  let buf ← stackAlloc 280
  let metas := buf + 40
  let infos := buf + 72
  let data  := buf + 184
  let sbuf  := buf + 208
  storeU8  data 0  IxOp.updateOracle
  storeU64 data 1  newP
  storeU8  data 9  fundSign
  storeU64 data 10 fundE6
  writeMeta metas        mkt         1 0
  writeMeta (metas + 16) oracAuthPda 0 1
  writeAccountInfo infos        mkt
  writeAccountInfo (infos + 56) oracAuthPda
  writeInstruction buf (AccountView.keyPtr percProg) metas 2 data 18
  let bump ← loadU8 aData AdpOff.pdaBump
  let signersArr ← writeOracPdaSeeds sbuf (AccountView.keyPtr adp) bump
  let rc ← sysInvokeSignedC buf infos 2 signersArr 1
  SolanaM.require (rc == 0) rc

def dispatch (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  let op ← loadU8 ix.ptr 0
  if op == 0 then handleInitAdapter input
  else if op == 1 then handleCrank input
  else SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (dispatch input) s

end Percolator.OracleAdapter
