/-
  Percolator.EvilMatcher
  Test-only adversarial PropAMM binary (NOT part of production deployment!) used exclusively
  by LiteSVM Suite 14 to attack unified single/multi-market `percolator::TradeWithMatcher`
  with every real-world malicious PropAMM exploit vector:
    attackMode 0: Over-fill (`fillQty = maxQty + 1`)
    attackMode 1: Abusive fill price violating taker `limitPrice`
    attackMode 2: Nonzero error `status = 7`
    attackMode 3: Stale / `noop.so` replay (`seq` unchanged)
    attackMode 4: Bad return magic (`0xDEADBEEF`)
    attackMode 5: Zero fill (`fillQty = 0`)
    attackMode 6: Exceed core `maxMoveBps` clamp (`execPrice = markP * 2`, with `limitPrice = 0`)
    attackMode 7: Attempt to write to readonly `extraAcc` (fails VM write-protection!)
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.EvilMatcher

open LeanSVM
open LeanSVM.Input
open Percolator

def handleEvil (input : Ptr) : SolanaM Unit := do
  let (n, ctx, ix, _) ← parseIxOnly input
  SolanaM.require (n >= 1 && ix.len >= 80) Err.invalidInstructionData
  let d := AccountView.dataPtr ctx
  let attackMode  ← loadU8 d 48
  let reqSeq      ← loadU64 ix.ptr 24
  let mode        ← loadU8  ix.ptr 32
  let takerIsLong ← loadU8  ix.ptr 33
  let maxQty      ← loadU64 ix.ptr 48
  let limitPrice  ← loadU64 ix.ptr 56
  let markP       ← loadU64 ix.ptr 64
  let isBuying := (mode == 0 && takerIsLong != 0) || (mode == 1 && takerIsLong == 0)
  if attackMode == 0 then
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  0
    storeU64 d 8  reqSeq
    storeU64 d 16 markP
    storeU64 d 24 (maxQty + 1)
  else if attackMode == 1 then
    let badP := if isBuying then limitPrice + 1 else (if limitPrice > 1 then limitPrice - 1 else 1)
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  0
    storeU64 d 8  reqSeq
    storeU64 d 16 badP
    storeU64 d 24 maxQty
  else if attackMode == 2 then
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  7
    storeU64 d 8  reqSeq
    storeU64 d 16 markP
    storeU64 d 24 maxQty
  else if attackMode == 3 then
    -- Stale seq (does not update d[8..16]!)
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  0
    storeU64 d 16 markP
    storeU64 d 24 maxQty
  else if attackMode == 4 then
    storeU32 d 0  0xDEADBEEF
    storeU32 d 4  0
    storeU64 d 8  reqSeq
    storeU64 d 16 markP
    storeU64 d 24 maxQty
  else if attackMode == 5 then
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  0
    storeU64 d 8  reqSeq
    storeU64 d 16 markP
    storeU64 d 24 0
  else if attackMode == 6 then
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  0
    storeU64 d 8  reqSeq
    storeU64 d 16 (markP * 2)
    storeU64 d 24 maxQty
  else if attackMode == 7 then
    SolanaM.require (n >= 2) Err.notEnoughAccountKeys
    let extraAcc ← AccountView.nextCursor ctx
    storeU8 (AccountView.dataPtr extraAcc) 0 0xFF
    storeU32 d 0  MAGIC_MRET
    storeU32 d 4  0
    storeU64 d 8  reqSeq
    storeU64 d 16 markP
    storeU64 d 24 maxQty
  else
    SolanaM.fail PErr.invalidInstruction

def entrypoint (input : Ptr) (s : SvmState) : UInt64 × SvmState :=
  SolanaM.runEntry (handleEvil input) s

end Percolator.EvilMatcher
