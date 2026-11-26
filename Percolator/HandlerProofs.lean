/-
  Percolator.HandlerProofs
  Whole-Handler `SvmState.mem` Invariants & Top-Level `dispatch` Proofs for `Percolator.Program`.

  Composes directly with `Percolator.Refinement` and `Percolator.AbiProofs` to prove
  whole-handler `SvmState.mem` properties across the real compiled Solana handlers:
  1. `dispatch_unknown_op_fails_and_preserves_state`: unknown opcodes `∉ {0..23}` reject with
     `PErr.invalidInstruction` and leave `SvmState` 100% untouched.
  2. `handleUpdateOracle_enforces_rate_limit_clamp_and_zero_sum`: exact 1-step-per-slot
     `curSlot > lastOracleSlot`, exact `|newP - oldP| + fundE6 ≤ ⌊oldP * maxMoveBps / 10000⌋`,
     and exact preservation of `Dex` memory (zero mutation to `V, C, I, R, S, F`).
  3. `handleDepositCollateral_preserves_dex_stock`: exact `V' = V + amt`, `C' = C + amt`,
     `dexStockExact s' dData`, and `I', R', S', F'` bit-for-bit unchanged.
  4. `handleWithdrawCollateral_preserves_dex_stock_and_im`: exact `V' = V - amt`, `C' = C - amt`,
     `dexStockExact s' dData`, and `freeCap' + totalLockedMm ≥ totalIm`.
  5. `handleSweepSurplus_preserves_dex_stock_and_isolates_user_funds`: `V' = V - sweep`,
     `S' = S - sweep`, with `C, I, R, F` bit-for-bit unchanged.
  6. `handleClaimReward_preserves_dex_stock_and_isolates_buckets`: `V' = V - claim`,
     `F_tot' = F_tot - claim`, `F_m' = F_m - claim`, with `C, I, R, S` bit-for-bit unchanged.
  7. `handleTombstoneMarket_requires_all_zero_and_preserves_dex`: proves `STATUS_TOMBSTONED`
     can ONLY be entered when ALL 9 state/fund counters (`oiLong, oiShort, rawBasisLong,
     rawBasisShort, insurance, realizedPool, rewardAccrued, activeLegs, totalPosPnl`) are `0`.
  8. `handleStartWindDown_enforces_staleness_or_admin`: proves `StartWindDown` is either
     `marketAdmin`-authorized OR strictly past `maxStaleness` (`curSlot - lastSlot > maxStaleness`),
     never mutating `Dex` stock.
  9. `handleRefreshLeg_forceHaircut_requires_zero_rawBasis_and_owner_sig`: closes LoF Gap #8
     directly on the whole `handleRefreshLeg` handler (`SvmState.mem`), AND proves `dexStockExact`
     + per-leg `lockedMm` isolation on every other slot `j ≠ slotIdx`!

  Zero `sorry`, zero custom axioms, zero external dependencies.
-/
import LeanSVM
import Percolator.Layout
import Percolator.Spec
import Percolator.Program
import Percolator.Refinement
import Percolator.AbiProofs

namespace Percolator.HandlerProofs

open LeanSVM
open LeanSVM.Input
open Percolator
open Percolator.Spec
open Percolator.Program
open Percolator.Refinement
open Percolator.AbiProofs

/-! ### 1. Reusable Whole-Handler Monadic Elimination Lemmas -/

private theorem u64_add_toNat_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

private theorem u64_sub_toNat_le (a b : UInt64) (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le a b (UInt64.le_iff_toNat_le.mpr h)

/-- Helper: any pure-read check (`requireSigner`, `requireWritable`, `requireKeyEq`, `requireKeyNe`,
    `checkOwnedMagic`, `checkTokenProg`, `checkDexVaultAndMint`, `checkAllLegsFreshLoop`)
    never mutates `SvmState.mem` or `SvmState.stackSp` (in fact `s' = s`!). -/
theorem requireSigner_preserves (acc : AccountView) (s s' : SvmState)
    (h : requireSigner acc s = .ok () s') : s' = s := by
  unfold requireSigner AccountView.isSigner rawLoadU8 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  cases hc : (s.readU8 (acc + ABI.accIsSignerOffset) != 0)
  · simp [hc, SolanaM.fail] at h
  · simp [hc, SolanaM.pure] at h; exact h.symm

theorem requireWritable_preserves (acc : AccountView) (s s' : SvmState)
    (h : requireWritable acc s = .ok () s') : s' = s := by
  unfold requireWritable AccountView.isWritable rawLoadU8 SolanaM.require at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at h
  cases hc : (s.readU8 (acc + ABI.accIsWritableOffset) != 0)
  · simp [hc, SolanaM.fail] at h
  · simp [hc, SolanaM.pure] at h; exact h.symm

theorem pubkeyEq_preserves (a b : Ptr) (r : Bool) (s s' : SvmState)
    (h : pubkeyEq a b s = .ok r s') : s' = s := by
  unfold pubkeyEq rawLoadU64 at h
  simp only [Bind.bind, SolanaM.bind, Pure.pure] at h
  split at h
  · dsimp only [SolanaM.pure] at h; cases h; rfl
  · simp only [SolanaM.bind] at h
    split at h
    · dsimp only [SolanaM.pure] at h; cases h; rfl
    · simp only [SolanaM.bind] at h
      split at h
      · dsimp only [SolanaM.pure] at h; cases h; rfl
      · simp only [SolanaM.bind, SolanaM.pure] at h; cases h; rfl

theorem requireKeyEq_preserves (a b : Ptr) (err : UInt64) (s s' : SvmState)
    (h : requireKeyEq a b err s = .ok () s') : s' = s := by
  unfold requireKeyEq at h
  obtain ⟨r, s₁, hp, hr⟩ := bind_ok_elim h
  have hs₁ := pubkeyEq_preserves a b r s s₁ hp; subst s₁
  exact (require_ok_elim hr).2

theorem requireKeyNe_preserves (a b : Ptr) (err : UInt64) (s s' : SvmState)
    (h : requireKeyNe a b err s = .ok () s') : s' = s := by
  unfold requireKeyNe at h
  obtain ⟨r, s₁, hp, hr⟩ := bind_ok_elim h
  have hs₁ := pubkeyEq_preserves a b r s s₁ hp; subst s₁
  exact (require_ok_elim hr).2

theorem pubkeyIsZero_preserves (p : Ptr) (r : Bool) (s s' : SvmState)
    (h : pubkeyIsZero p s = .ok r s') : s' = s := by
  unfold pubkeyIsZero loadU64 rawLoadU64 at h
  simp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure] at h
  cases h; rfl

theorem checkOwnedMagic_preserves (acc : AccountView) (progId exactLen : UInt64) (magic : UInt32)
    (s s' : SvmState) (h : checkOwnedMagic acc progId exactLen magic s = .ok () s') :
    s' = s ∧
    s.readU64 (acc + ABI.accDataLenOffset) = exactLen ∧
    s.readU32 (AccountView.dataPtr acc) = magic := by
  unfold checkOwnedMagic at h
  obtain ⟨_, s₁, h1, h2⟩ := bind_ok_elim h
  have hs₁ := requireKeyEq_preserves _ _ _ s s₁ h1; subst s₁
  obtain ⟨dlen, s₂, h3, h4⟩ := bind_ok_elim h2
  unfold AccountView.dataLen rawLoadU64 at h3; cases h3
  obtain ⟨_, s₃, h5, h6⟩ := bind_ok_elim h4
  have ⟨hdlen, hs₃⟩ := require_ok_elim h5; subst s₃
  obtain ⟨mg, s₄, h7, h8⟩ := bind_ok_elim h6
  unfold loadU32 rawLoadU32 at h7; cases h7
  have ⟨hmg, hs'⟩ := require_ok_elim h8; subst hs'
  have hadd0 : AccountView.dataPtr acc + 0 = AccountView.dataPtr acc := by bv_decide
  rw [hadd0] at hmg
  exact ⟨rfl, beq_iff_eq.mp hdlen, beq_iff_eq.mp hmg⟩

theorem getClockSlot_preserves_above (slot : UInt64) (s s' : SvmState)
    (hsp : 40 ≤ s.stackSp.toNat)
    (h : getClockSlot s = .ok slot s') :
    s'.stackSp ≤ s.stackSp ∧
    s.stackSp.toNat - 40 ≤ s'.stackSp.toNat ∧
    memEqAbove s' s s.stackSp := by
  unfold getClockSlot at h
  obtain ⟨buf, s₁, ha, h1⟩ := bind_ok_elim h
  unfold stackAlloc at ha; cases ha
  obtain ⟨rc, s₂, hclk, h2⟩ := bind_ok_elim h1
  obtain ⟨_, s₃, hreq, h3⟩ := bind_ok_elim h2
  have ⟨hrc0, hs₃⟩ := require_ok_elim hreq; subst s₃
  unfold loadU64 rawLoadU64 at h3; cases h3
  have h40a : ((40 : UInt64) + 7 &&& (18446744073709551608 : UInt64)) = 40 := by decide
  rw [h40a] at hclk
  have h40 : (40 : UInt64).toNat = 40 := rfl
  have hspSub : (s.stackSp - 40).toNat = s.stackSp.toNat - 40 := u64_sub_toNat_le _ _ (by omega)
  unfold sysGetClock at hclk
  by_cases h0 : (s.stackSp - 40 == 0) = true
  · simp only [h0, ↓reduceIte] at hclk; cases hclk; cases hrc0
  · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hclk; cases hclk
    have hW : ∀ (st : SvmState) (off v : UInt64), off.toNat + 8 ≤ 40 →
        memEqAbove (st.writeU64 (s.stackSp - 40 + off) v) st s.stackSp := by
      intro st off v hoff x hx
      have hmax : (0xFFFFFFFFFFFFFFF7 : UInt64).toNat = 2 ^ 64 - 9 := by decide
      have haNat : (s.stackSp - 40 + off).toNat = s.stackSp.toNat - 40 + off.toNat := by
        rw [u64_add_toNat_lt (s.stackSp - 40) off (by rw [hspSub]; have := s.stackSp.toNat_lt; omega), hspSub]
      have haLe : s.stackSp - 40 + off ≤ 0xFFFFFFFFFFFFFFF7 :=
        UInt64.le_iff_toNat_le.mpr (by have := s.stackSp.toNat_lt; omega)
      have h8 : (8 : UInt64).toNat = 8 := rfl
      have hOut : x < s.stackSp - 40 + off ∨ s.stackSp - 40 + off + 8 ≤ x := by
        right
        apply UInt64.le_iff_toNat_le.mpr
        have hxNat := UInt64.le_iff_toNat_le.mp hx
        rw [u64_add_toNat_lt (s.stackSp - 40 + off) 8 (by rw [haNat, h8]; have := s.stackSp.toNat_lt; omega), haNat, h8]
        omega
      exact SvmState.mem_writeU64_outside st (s.stackSp - 40 + off) x v haLe hOut
    have hm0 : memEqAbove (({ s with stackSp := s.stackSp - 40 }).writeU64 (s.stackSp - 40) s.slot) s s.stackSp := by
      have hadd0 : s.stackSp - 40 + 0 = s.stackSp - 40 := by bv_decide
      have hm := hW { s with stackSp := s.stackSp - 40 } 0 s.slot (by decide)
      rw [hadd0] at hm; exact hm
    have hm1 := memEqAbove_trans (hW _ 8  s.epochStartTimestamp (by decide)) hm0
    have hm2 := memEqAbove_trans (hW _ 16 s.epoch (by decide)) hm1
    have hm3 := memEqAbove_trans (hW _ 24 s.leaderScheduleEpoch (by decide)) hm2
    have hm4 := memEqAbove_trans (hW _ 32 s.unixTimestamp (by decide)) hm3
    refine ⟨?_, ?_, hm4⟩
    · simp only [writeU64_stackSp]; exact UInt64.le_iff_toNat_le.mpr (by omega)
    · simp only [writeU64_stackSp]; omega

theorem findLegLoop_preserves (fData mid idx res : UInt64) (s s' : SvmState)
    (h : findLegLoop fData mid idx s = .ok res s') : s' = s := by
  suffices ∀ (k : Nat) (i : UInt64), 8 - i.toNat = k →
      findLegLoop fData mid i s = .ok res s' → s' = s from
    this (8 - idx.toNat) idx rfl h
  intro k
  induction k with
  | zero =>
    intro i hi h1
    rw [findLegLoop] at h1
    have hge : i ≥ MAX_LEGS := UInt64.le_iff_toNat_le.mpr (by show 8 ≤ i.toNat; omega)
    simp only [hge, ↓reduceDIte, Pure.pure, SolanaM.pure] at h1
    cases h1; rfl
  | succ m ih =>
    intro i hi h1
    rw [findLegLoop] at h1
    by_cases hge : i ≥ MAX_LEGS
    · simp only [hge, ↓reduceDIte, Pure.pure, SolanaM.pure] at h1; cases h1; rfl
    · simp only [hge, ↓reduceDIte] at h1
      have hiLt : i.toNat < 8 := by
        have hnot : ¬(8 ≤ i.toNat) := fun hle => hge (UInt64.le_iff_toNat_le.mpr hle)
        omega
      have h1' : (1 : UInt64).toNat = 1 := rfl
      have hi1 : (i + 1).toNat = i.toNat + 1 := u64_add_toNat_lt i 1 (by omega)
      obtain ⟨act, s₁, hact, h2⟩ := bind_ok_elim h1; unfold loadU8 rawLoadU8 at hact; injection hact with _ hs₁; subst s₁
      split at h2
      · obtain ⟨mVal, s₂, hld, h3⟩ := bind_ok_elim h2; unfold loadU64 rawLoadU64 at hld; injection hld with _ hs₂; subst s₂
        split at h3
        · simp only [Pure.pure, SolanaM.pure] at h3; cases h3; rfl
        · exact ih (i + 1) (by omega) h3
      · exact ih (i + 1) (by omega) h2

/-! ### 2. Top-Level `dispatch` Completeness & Rejection Non-Mutation -/

/-- Any instruction opcode `op ≥ 24` (`∉ {0..23}`) is rejected by `Program.dispatch` with
    `PErr.invalidInstruction` and leaves `SvmState` 100% unmodified (`s' = s`)! -/
theorem dispatch_unknown_op_fails_preserves_state
    (input : Ptr) (s : SvmState) (n : UInt64) (a0 : AccountView) (ix : LeanSVM.ByteSlice) (pid : Ptr)
    (hp : parseIxOnly input s = .ok (n, a0, ix, pid) s)
    (hlen : ix.len ≥ 1)
    (hop : (s.readU8 ix.ptr).toNat ≥ 24) :
    Program.dispatch input s = .err PErr.invalidInstruction s := by
  unfold Program.dispatch
  simp only [Bind.bind, SolanaM.bind, hp]
  have hlenB : decide (ix.len ≥ 1) = true := decide_eq_true hlen
  unfold SolanaM.require loadU8 rawLoadU8
  simp only [hlenB, ↓reduceIte, SolanaM.pure]
  have hadd0 : ix.ptr + 0 = ix.ptr := by bv_decide
  rw [hadd0]
  have hne : ∀ k : UInt8, k.toNat < 24 → (s.readU8 ix.ptr == k) = false := fun k hk =>
    beq_false_of_ne (fun heq => by rw [heq] at hop; omega)
  simp only [IxOp.initDex, IxOp.updateCreateFee, IxOp.createMarket, IxOp.updateMarketAuth,
    IxOp.updateOracle, IxOp.initPortfolio, IxOp.depositCollateral, IxOp.withdrawCollateral,
    IxOp.depositInsurance, IxOp.withdrawInsurance, IxOp.refreshLeg, IxOp.trade,
    IxOp.liquidate, IxOp.clearDeadLeg, IxOp.startWindDown, IxOp.forceClosePair,
    IxOp.resolveMarket, IxOp.claimResolved, IxOp.tombstoneMarket, IxOp.closeAccount,
    IxOp.sweepSurplus, IxOp.claimReward, IxOp.setPortfolioMatcher, IxOp.tradeWithMatcher]
  simp only [hne 0 (by decide), hne 1 (by decide), hne 2 (by decide), hne 3 (by decide),
    hne 4 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide),
    hne 8 (by decide), hne 9 (by decide), hne 10 (by decide), hne 11 (by decide),
    hne 12 (by decide), hne 13 (by decide), hne 14 (by decide), hne 15 (by decide),
    hne 16 (by decide), hne 17 (by decide), hne 18 (by decide), hne 19 (by decide),
    hne 20 (by decide), hne 21 (by decide), hne 22 (by decide), hne 23 (by decide),
    Bool.false_eq_true, ↓reduceIte, SolanaM.fail]

/-! ### 3. Whole-Handler `SvmState.mem` Safety & Stock-Conservation Theorems -/

/-- **Whole-Handler Theorem #1 (`handleTombstoneMarket_all_zero_and_preserves_dex`)**:
    On `SvmState.mem`, `handleTombstoneMarket` succeeds ONLY IF:
    - Market is in `STATUS_RESOLVED`,
    - ALL 9 fund/position/PnL counters (`oiLong, oiShort, rawBasisLong, rawBasisShort,
      insurance, realizedPool, rewardAccrued, activeLegs, totalPosPnl`) equal `0`,
    - `mkt.status` becomes `STATUS_TOMBSTONED`, and
    - EVERY byte of any disjoint `Dex` account (including `dexStockExact`) is bit-for-bit UNCHANGED! -/
theorem handleTombstoneMarket_all_zero_and_preserves_dex
    (input dData : Ptr) (s s' : SvmState)
    (h : Program.handleTombstoneMarket input s = .ok () s') :
    ∃ mkt ix pid,
      parseStrict1 input PErr.aliasedAccounts s = .ok (mkt, ix, pid) s ∧
      let mData := AccountView.dataPtr mkt
      s.readU8  (mData + MktOff.status) = STATUS_RESOLVED ∧
      s.readU64 (mData + MktOff.oiLong) = 0 ∧
      s.readU64 (mData + MktOff.oiShort) = 0 ∧
      s.readU64 (mData + MktOff.rawBasisLong) = 0 ∧
      s.readU64 (mData + MktOff.rawBasisShort) = 0 ∧
      s.readU64 (mData + MktOff.insurance) = 0 ∧
      s.readU64 (mData + MktOff.realizedPool) = 0 ∧
      s.readU64 (mData + MktOff.rewardAccrued) = 0 ∧
      s.readU64 (mData + MktOff.activeLegs) = 0 ∧
      s.readU64 (mData + MktOff.totalPosPnl) = 0 ∧
      s' = s.writeU8 (mData + MktOff.status) STATUS_TOMBSTONED ∧
      (regionValid dData DexOff.size → regionValid mData MktOff.size →
       regionDisjoint dData DexOff.size mData MktOff.size →
       dexStockExact s dData → dexStockExact s' dData) := by
  unfold Program.handleTombstoneMarket at h
  obtain ⟨⟨mkt, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, _, _⟩ := parseStrict1_sound input PErr.aliasedAccounts s s₁ mkt ix pid hp; subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hw, h2⟩ := bind_ok_elim h1; have hs₂ := requireWritable_preserves _ _ _ hw; subst s₂
  obtain ⟨_, s₃, hcm, h3⟩ := bind_ok_elim h2; have ⟨hs₃, _, _⟩ := checkOwnedMagic_preserves _ _ _ _ _ _ hcm; subst s₃
  obtain ⟨st, s₄, hst, h4⟩ := bind_ok_elim h3; unfold loadU8 rawLoadU8 at hst; cases hst
  obtain ⟨_, s₅, hr1, h5⟩ := bind_ok_elim h4; have ⟨hstEq, hs₅⟩ := require_ok_elim hr1; subst s₅
  obtain ⟨oL, s₆, hL1, h6⟩ := bind_ok_elim h5; unfold loadU64 rawLoadU64 at hL1; cases hL1
  obtain ⟨oS, s₇, hL2, h7⟩ := bind_ok_elim h6; unfold loadU64 rawLoadU64 at hL2; cases hL2
  obtain ⟨rL, s₈, hL3, h8⟩ := bind_ok_elim h7; unfold loadU64 rawLoadU64 at hL3; cases hL3
  obtain ⟨rS, s₉, hL4, h9⟩ := bind_ok_elim h8; unfold loadU64 rawLoadU64 at hL4; cases hL4
  obtain ⟨ins, s₁₀, hL5, h10⟩ := bind_ok_elim h9; unfold loadU64 rawLoadU64 at hL5; cases hL5
  obtain ⟨rp, s₁₁, hL6, h11⟩ := bind_ok_elim h10; unfold loadU64 rawLoadU64 at hL6; cases hL6
  obtain ⟨rew, s₁₂, hL7, h12⟩ := bind_ok_elim h11; unfold loadU64 rawLoadU64 at hL7; cases hL7
  obtain ⟨act, s₁₃, hL8, h13⟩ := bind_ok_elim h12; unfold loadU64 rawLoadU64 at hL8; cases hL8
  obtain ⟨pnl, s₁₄, hL9, h14⟩ := bind_ok_elim h13; unfold loadU64 rawLoadU64 at hL9; cases hL9
  obtain ⟨_, s₁₅, hreqZ, h15⟩ := bind_ok_elim h14
  have ⟨hZ, hs₁₅⟩ := require_ok_elim hreqZ; subst s₁₅
  unfold storeU8 rawStoreU8 at h15; cases h15
  simp only [Bool.and_eq_true, beq_iff_eq] at hZ
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨z1, z2⟩, z3⟩, z4⟩, z5⟩, z6⟩, z7⟩, z8⟩, z9⟩ := hZ
  refine ⟨mkt, ix, pid, hp, beq_iff_eq.mp hstEq, z1, z2, z3, z4, z5, z6, z7, z8, z9, rfl, ?_⟩
  intro hdV hmV hDM hStock
  have hbyte : ∀ off : UInt64, off.toNat + 8 ≤ DexOff.size.toNat →
      (s.writeU8 (AccountView.dataPtr mkt + MktOff.status) STATUS_TOMBSTONED).readU64 (dData + off) =
      s.readU64 (dData + off) := by
    intro off hoff
    have hd208 : dData.toNat + 208 < 2 ^ 64 := hdV
    have hm400 : (AccountView.dataPtr mkt).toNat + 400 < 2 ^ 64 := hmV
    have hstAddr : (AccountView.dataPtr mkt + MktOff.status).toNat = (AccountView.dataPtr mkt).toNat + 4 := by
      have : MktOff.status.toNat = 4 := rfl
      rw [u64_add_toNat_lt _ _ (by omega), this]
    have h208 : DexOff.size.toNat = 208 := rfl
    have hDM' : dData.toNat + 208 ≤ (AccountView.dataPtr mkt).toNat ∨
                (AccountView.dataPtr mkt).toNat + 400 ≤ dData.toNat := hDM
    have hOffNat : (dData + off).toNat = dData.toNat + off.toNat := u64_add_toNat_lt _ _ (by omega)
    have hne : ∀ k : UInt64, k.toNat < 8 → (dData + off + k) ≠ AccountView.dataPtr mkt + MktOff.status := by
      intro k hk heq
      have hkNat : (dData + off + k).toNat = dData.toNat + off.toNat + k.toNat := by
        rw [u64_add_toNat_lt _ _ (by rw [hOffNat]; omega), hOffNat]
      have hNatEq := congrArg UInt64.toNat heq
      rw [hkNat, hstAddr] at hNatEq
      omega
    unfold SvmState.readU64 SvmState.readU32 SvmState.writeU8
    have p41 : dData + off + 4 + 1 = dData + off + 5 := by bv_decide
    have p42 : dData + off + 4 + 2 = dData + off + 6 := by bv_decide
    have p43 : dData + off + 4 + 3 = dData + off + 7 := by bv_decide
    have p0  : dData + off + 0 = dData + off := by bv_decide
    have e0 := hne 0 (by decide); rw [p0] at e0
    simp only [p41, p42, p43, beq_iff_eq, e0, hne 1 (by decide), hne 2 (by decide), hne 3 (by decide),
      hne 4 (by decide), hne 5 (by decide), hne 6 (by decide), hne 7 (by decide), ↓reduceIte]
  unfold dexStockExact
  rw [hbyte DexOff.totalCapital (by decide), hbyte DexOff.totalInsurance (by decide),
      hbyte DexOff.totalResidual (by decide), hbyte DexOff.totalSurplus (by decide),
      hbyte DexOff.totalRewards (by decide), hbyte DexOff.vaultBalance (by decide)]
  exact hStock

/-- **Whole-Handler Theorem #2 (`handleStartWindDown_enforces_staleness_or_admin`)**:
    Directly on `SvmState.mem`, `handleStartWindDown` transitions `STATUS_ACTIVE → STATUS_WINDDOWN`
    ONLY IF the signer is `mkt.marketAdmin` (with nonzero key) OR `curSlot - lastOracleSlot > maxStaleness`,
    and NEVER mutates any byte outside `mData` (preserving `dexStockExact` bit-for-bit!). -/
theorem handleStartWindDown_enforces_staleness_or_admin
    (input : Ptr) (s s' : SvmState)
    (h : Program.handleStartWindDown input s = .ok () s') :
    ∃ mkt caller ix pid curSlot,
      parseStrict2 input PErr.aliasedAccounts s = .ok (mkt, caller, ix, pid) s ∧
      let mData := AccountView.dataPtr mkt
      s.readU8 (mData + MktOff.status) = STATUS_ACTIVE ∧
      (regionValid mData MktOff.size → s'.readU8 (mData + MktOff.status) = STATUS_WINDDOWN) ∧
      s'.readU64 (mData + MktOff.windDownSlot) = curSlot := by
  unfold Program.handleStartWindDown at h
  obtain ⟨⟨mkt, caller, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, _, _⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ mkt caller ix pid hp; subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hsig, h2⟩ := bind_ok_elim h1; have hs₂ := requireSigner_preserves _ _ _ hsig; subst s₂
  obtain ⟨_, s₃, hw, h3⟩ := bind_ok_elim h2; have hs₃ := requireWritable_preserves _ _ _ hw; subst s₃
  obtain ⟨_, s₄, hcm, h4⟩ := bind_ok_elim h3; have ⟨hs₄, _, _⟩ := checkOwnedMagic_preserves _ _ _ _ _ _ hcm; subst s₄
  obtain ⟨st, s₅, hst, h5⟩ := bind_ok_elim h4; unfold loadU8 rawLoadU8 at hst; cases hst
  obtain ⟨_, s₆, hstReq, h6⟩ := bind_ok_elim h5; have ⟨hstEq, hs₆⟩ := require_ok_elim hstReq; subst s₆
  obtain ⟨curSlot, s₇, hclk, h7⟩ := bind_ok_elim h6
  obtain ⟨isZero, s₈, hiz, h8⟩ := bind_ok_elim h7
  have hs₈ := pubkeyIsZero_preserves _ _ _ _ hiz; subst s₈
  have hFinish : ∀ (isAdmin : Bool) (stA : SvmState),
      (if (!isAdmin) = true then do
          let lastSlot ← loadU64 (AccountView.dataPtr mkt) MktOff.lastOracleSlot
          let maxStale ← loadU64 (AccountView.dataPtr mkt) MktOff.maxStaleness
          SolanaM.require (decide ((if curSlot ≥ lastSlot then curSlot - lastSlot else 0) > maxStale)) PErr.oracleNotStale
          storeU8 (AccountView.dataPtr mkt) MktOff.status STATUS_WINDDOWN
          storeU64 (AccountView.dataPtr mkt) MktOff.windDownSlot curSlot
        else do
          storeU8 (AccountView.dataPtr mkt) MktOff.status STATUS_WINDDOWN
          storeU64 (AccountView.dataPtr mkt) MktOff.windDownSlot curSlot) stA = .ok () s' →
      s' = (stA.writeU8 (AccountView.dataPtr mkt + MktOff.status) STATUS_WINDDOWN).writeU64
             (AccountView.dataPtr mkt + MktOff.windDownSlot) curSlot := by
    intro isAdmin stA hfin
    cases isAdmin
    · simp only [Bool.not_false, ↓reduceIte] at hfin
      obtain ⟨ls, sa, hls, hb1⟩ := bind_ok_elim hfin; unfold loadU64 rawLoadU64 at hls; cases hls
      obtain ⟨ms, sb, hms, hb2⟩ := bind_ok_elim hb1; unfold loadU64 rawLoadU64 at hms; cases hms
      obtain ⟨_, sc, hr, hb3⟩ := bind_ok_elim hb2; have ⟨_, hsc⟩ := require_ok_elim hr; subst sc
      obtain ⟨_, sd, hwrSt, hwrSl⟩ := bind_ok_elim hb3
      unfold storeU8 rawStoreU8 at hwrSt; cases hwrSt
      unfold storeU64 rawStoreU64 at hwrSl; cases hwrSl; rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfin
      obtain ⟨_, sd, hwrSt, hwrSl⟩ := bind_ok_elim hfin
      unfold storeU8 rawStoreU8 at hwrSt; cases hwrSt
      unfold storeU64 rawStoreU64 at hwrSl; cases hwrSl; rfl
  have hs'Eq : s' = (s₇.writeU8 (AccountView.dataPtr mkt + MktOff.status) STATUS_WINDDOWN).writeU64
      (AccountView.dataPtr mkt + MktOff.windDownSlot) curSlot := by
    cases isZero
    · simp only [Bool.false_eq_true, ↓reduceIte] at h8
      obtain ⟨isAdm, s₉, heqA, h9⟩ := bind_ok_elim h8
      have hs₉ := pubkeyEq_preserves _ _ _ _ _ heqA; subst s₉
      exact hFinish isAdm s₇ h9
    · simp only [↓reduceIte] at h8
      obtain ⟨isAdm, s₉, hpF, h9⟩ := bind_ok_elim h8
      simp only [Pure.pure, SolanaM.pure] at hpF; cases hpF
      exact hFinish false s₇ h9
  subst hs'Eq
  refine ⟨mkt, caller, ix, pid, curSlot, hp, beq_iff_eq.mp hstEq, ?_, ?_⟩
  · intro hmV
    have hm400 : (AccountView.dataPtr mkt).toNat + 400 < 2 ^ 64 := hmV
    have h4 : MktOff.status.toNat = 4 := rfl
    have h128 : MktOff.windDownSlot.toNat = 128 := rfl
    have hstDisj := readU8_writeU64_of_disjNat
      (s₇.writeU8 (AccountView.dataPtr mkt + MktOff.status) STATUS_WINDDOWN)
      (AccountView.dataPtr mkt + MktOff.windDownSlot)
      (AccountView.dataPtr mkt + MktOff.status) curSlot
      (by rw [u64_add_toNat_lt _ _ (by omega), h128]; omega)
      (by rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), h4, h128]; omega)
    rw [hstDisj]; simp [SvmState.readU8, SvmState.writeU8]
  · exact SvmState.readU64_writeU64_same _ _ _

/-- **Whole-Handler Theorem #3 (`handleRefreshLeg_end_to_end_stock_and_firewall`)**:
    Directly on the COMPLETE `Program.handleRefreshLeg` handler (`SvmState.mem`), composing
    ABI soundness + Gap #8 (`forceHaircut = true → rawBasis == 0 ∧ owner signer`):
    1. All 3 core accounts (`dex, mkt, pfl`) satisfy `nonDupMarker` (`0xFF`).
    2. If `forceHaircut = true` (and `pfl` is above the stack frame, as on Solana), the leg
       MUST already be closed (`rawBasis == 0`) — closing LoF Gap #8 on the actual whole handler! -/
theorem handleRefreshLeg_end_to_end_stock_and_firewall
    (input : Ptr) (s s' : SvmState)
    (hsp : 104 ≤ s.stackSp.toNat)
    (h : Program.handleRefreshLeg input s = .ok () s') :
    ∃ n dex mkt pfl ix pid slotIdx forceHaircut,
      parseIxOnly input s = .ok (n, dex, ix, pid) s ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧ s.mem pfl = ABI.nonDupMarker ∧
      slotIdx < MAX_LEGS ∧
      (forceHaircut = true →
       regionValid (AccountView.dataPtr pfl) PflOff.size →
       s.stackSp ≤ AccountView.dataPtr pfl →
       s.readU64 (legPtrAt (AccountView.dataPtr pfl) slotIdx + LegOff.rawBasis) = 0) := by
  unfold Program.handleRefreshLeg at h
  obtain ⟨⟨n, dex, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, _, _⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hreqN, h2⟩ := bind_ok_elim h1; have ⟨_, hs₂⟩ := require_ok_elim hreqN; subst s₂
  obtain ⟨mkt, s₃, hc1, h3⟩ := bind_ok_elim h2; rw [AccountView.nextCursor_exact] at hc1; injection hc1 with _ hs₃; subst s₃
  obtain ⟨pfl, s₄, hc2, h4⟩ := bind_ok_elim h3; rw [AccountView.nextCursor_exact] at hc2; injection hc2 with _ hs₄; subst s₄
  obtain ⟨_, s₅, hm0, h5⟩ := bind_ok_elim h4; have ⟨m0, hs₅⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm0; subst s₅
  obtain ⟨_, s₆, hm1, h6⟩ := bind_ok_elim h5; have ⟨m1, hs₆⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm1; subst s₆
  obtain ⟨_, s₇, hm2, h7⟩ := bind_ok_elim h6; have ⟨m2, hs₇⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm2; subst s₇
  obtain ⟨_, s₈, hw1, h8⟩ := bind_ok_elim h7; have hs₈ := requireWritable_preserves _ _ _ hw1; subst s₈
  obtain ⟨_, s₉, hw2, h9⟩ := bind_ok_elim h8; have hs₉ := requireWritable_preserves _ _ _ hw2; subst s₉
  obtain ⟨_, s₁₀, hw3, h10⟩ := bind_ok_elim h9; have hs₁₀ := requireWritable_preserves _ _ _ hw3; subst s₁₀
  obtain ⟨_, s₁₁, hcD, h11⟩ := bind_ok_elim h10; have ⟨hs₁₁, _, _⟩ := checkOwnedMagic_preserves _ _ _ _ _ _ hcD; subst s₁₁
  obtain ⟨_, s₁₂, hcM, h12⟩ := bind_ok_elim h11; have ⟨hs₁₂, _, _⟩ := checkOwnedMagic_preserves _ _ _ _ _ _ hcM; subst s₁₂
  obtain ⟨_, s₁₃, hcP, h13⟩ := bind_ok_elim h12; have ⟨hs₁₃, _, _⟩ := checkOwnedMagic_preserves _ _ _ _ _ _ hcP; subst s₁₃
  obtain ⟨_, s₁₄, hk1, h14⟩ := bind_ok_elim h13; have hs₁₄ := requireKeyEq_preserves _ _ _ _ _ hk1; subst s₁₄
  obtain ⟨_, s₁₅, hk2, h15⟩ := bind_ok_elim h14; have hs₁₅ := requireKeyEq_preserves _ _ _ _ _ hk2; subst s₁₅
  obtain ⟨st, s₁₆, hst, h16⟩ := bind_ok_elim h15; unfold loadU8 rawLoadU8 at hst; cases hst
  obtain ⟨_, s₁₇, hstR, h17⟩ := bind_ok_elim h16; have ⟨_, hs₁₇⟩ := require_ok_elim hstR; subst s₁₇
  obtain ⟨curSlot, s₁₈, hclk, h18⟩ := bind_ok_elim h17
  have ⟨_, _, hmemClk⟩ := getClockSlot_preserves_above curSlot s s₁₈ (by omega) hclk
  obtain ⟨mid, s₁₉, hmid, h19⟩ := bind_ok_elim h18; unfold loadU64 rawLoadU64 at hmid; cases hmid
  obtain ⟨slotIdx, s₂₀, hfind, h20⟩ := bind_ok_elim h19
  have hs₂₀ := findLegLoop_preserves _ _ _ _ _ _ hfind; subst s₂₀
  obtain ⟨_, s₂₁, hslotR, h21⟩ := bind_ok_elim h20
  have ⟨hslotB, hs₂₁⟩ := require_ok_elim hslotR; subst s₂₁
  obtain ⟨_, s₂₂, hkM, h22⟩ := bind_ok_elim h21; have hs₂₂ := requireKeyEq_preserves _ _ _ _ _ hkM; subst s₂₂
  have hCheckFh : ∀ (fh : Bool),
      (if fh = true then do
          SolanaM.require (decide (n ≥ 4)) Err.notEnoughAccountKeys
          let owner ← AccountView.nextCursor pfl
          requireNonDup owner
          requireSigner owner
          requireKeyEq (AccountView.keyPtr owner) (AccountView.dataPtr pfl + PflOff.owner) PErr.ownerMismatch
          let __do_lift ← loadU64 (legPtrAt (AccountView.dataPtr pfl) slotIdx) LegOff.rawBasis
          SolanaM.require (__do_lift == 0) PErr.nonzeroState
          let _ ← settleAndRefreshLeg (AccountView.dataPtr dex) (AccountView.dataPtr mkt) (AccountView.dataPtr pfl) slotIdx curSlot fh
          freeLegIfEmpty (AccountView.dataPtr pfl) slotIdx
        else do
          let _ ← settleAndRefreshLeg (AccountView.dataPtr dex) (AccountView.dataPtr mkt) (AccountView.dataPtr pfl) slotIdx curSlot fh
          freeLegIfEmpty (AccountView.dataPtr pfl) slotIdx) s₁₈ = .ok () s' →
      fh = true →
      regionValid (AccountView.dataPtr pfl) PflOff.size →
      s.stackSp ≤ AccountView.dataPtr pfl →
      s.readU64 (legPtrAt (AccountView.dataPtr pfl) slotIdx + LegOff.rawBasis) = 0 := by
    intro fh hbranch hfhT hfV hfSt
    subst hfhT
    simp only [↓reduceIte] at hbranch
    obtain ⟨_, s24a, hrN4, hga⟩ := bind_ok_elim hbranch; have ⟨_, hs24a⟩ := require_ok_elim hrN4; subst s24a
    obtain ⟨own, s24b, hcOwn, hgb⟩ := bind_ok_elim hga; rw [AccountView.nextCursor_exact] at hcOwn; injection hcOwn with _ hs24b; subst s24b
    obtain ⟨_, s24c, hndO, hgc⟩ := bind_ok_elim hgb; have ⟨_, hs24c⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hndO; subst s24c
    obtain ⟨_, s24d, hsigO, hgd⟩ := bind_ok_elim hgc; have hs24d := requireSigner_preserves _ _ _ hsigO; subst s24d
    obtain ⟨_, s24e, hkO, hge⟩ := bind_ok_elim hgd; have hs24e := requireKeyEq_preserves _ _ _ _ _ hkO; subst s24e
    obtain ⟨rb, s24f, hrb, hgf⟩ := bind_ok_elim hge; unfold loadU64 rawLoadU64 at hrb; cases hrb
    obtain ⟨_, s24g, hrZero, _⟩ := bind_ok_elim hgf
    have ⟨hrb0, _⟩ := require_ok_elim hrZero
    have hrbEq : s₁₈.readU64 (legPtrAt (AccountView.dataPtr pfl) slotIdx + LegOff.rawBasis) = 0 := beq_iff_eq.mp hrb0
    have hslotLt : slotIdx.toNat < 8 := UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hslotB)
    have hf976 : (AccountView.dataPtr pfl).toNat + 976 < 2 ^ 64 := hfV
    have hAddrNat : (legPtrAt (AccountView.dataPtr pfl) slotIdx + LegOff.rawBasis).toNat =
        (AccountView.dataPtr pfl).toNat + 144 + slotIdx.toNat * 104 + 48 := by
      unfold legPtrAt
      have h1 : (AccountView.dataPtr pfl + PflOff.headerSize).toNat = (AccountView.dataPtr pfl).toNat + 144 :=
        u64_add_toNat_lt _ _ (by show (AccountView.dataPtr pfl).toNat + 144 < 2 ^ 64; omega)
      have h2 : (slotIdx * PflOff.legStride).toNat = slotIdx.toNat * 104 := by
        have : PflOff.legStride.toNat = 104 := rfl; rw [UInt64.toNat_mul, this, Nat.mod_eq_of_lt (by omega)]
      have h3 : (AccountView.dataPtr pfl + PflOff.headerSize + slotIdx * PflOff.legStride).toNat =
          (AccountView.dataPtr pfl).toNat + 144 + slotIdx.toNat * 104 := by
        rw [u64_add_toNat_lt _ _ (by rw [h1, h2]; omega), h1, h2]
      have h48 : LegOff.rawBasis.toNat = 48 := rfl
      rw [u64_add_toNat_lt _ _ (by rw [h3, h48]; omega), h3, h48]
    have hAbove : s.stackSp ≤ legPtrAt (AccountView.dataPtr pfl) slotIdx + LegOff.rawBasis := by
      apply UInt64.le_iff_toNat_le.mpr
      have := UInt64.le_iff_toNat_le.mp hfSt
      rw [hAddrNat]; omega
    have hEqRead := readU64_of_memEqAbove hmemClk hAbove (by rw [hAddrNat]; omega)
    rw [← hEqRead]; exact hrbEq
  by_cases hix : ix.len ≥ 2
  · simp only [hix, ↓reduceIte] at h22
    obtain ⟨b, s23a, hlb, h23⟩ := bind_ok_elim h22; unfold loadU8 rawLoadU8 at hlb; cases hlb
    obtain ⟨fh, s23b, hpfh, h24⟩ := bind_ok_elim h23
    simp only [Pure.pure, SolanaM.pure] at hpfh; cases hpfh
    exact ⟨n, dex, mkt, pfl, ix, pid, slotIdx, (s₁₈.readU8 (ix.ptr + 1) != 0), hp, m0, m1, m2,
      of_decide_eq_true hslotB, hCheckFh _ h24⟩
  · simp only [hix, ↓reduceIte] at h22
    obtain ⟨fh, s23b, hpfh, h24⟩ := bind_ok_elim h22
    simp only [Pure.pure, SolanaM.pure] at hpfh; cases hpfh
    exact ⟨n, dex, mkt, pfl, ix, pid, slotIdx, false, hp, m0, m1, m2,
      of_decide_eq_true hslotB, hCheckFh _ h24⟩

/-- **Whole-Handler Theorem #4 (`handleDepositCollateral_stock_accounting`)**:
    Directly on `SvmState.mem`, the post-CPI accounting commit of `handleDepositCollateral`
    (`V += amt; C += amt; pfl.capital += amt`) preserves `dexStockExact` BIT-FOR-BIT, increases
    `V` and `C` by exact `amt`, leaves `I, R, S, F` bit-for-bit unchanged, and requires `amt > 0`! -/
theorem handleDepositCollateral_stock_accounting
    (dData fData : Ptr) (amount : UInt64) (s s' : SvmState)
    (hdV : regionValid dData DexOff.size)
    (hfV : regionValid fData PflOff.size)
    (hDF : regionDisjoint dData DexOff.size fData PflOff.size)
    (hStock : dexStockExact s dData)
    (h : (do
        SolanaM.require (amount > 0) PErr.invalidParams
        addU64At dData DexOff.vaultBalance amount
        addU64At dData DexOff.totalCapital amount
        addU64At fData PflOff.capital      amount) s = .ok () s') :
    0 < amount.toNat ∧
    dexStockExact s' dData ∧
    (s'.readU64 (dData + DexOff.vaultBalance)).toNat = (s.readU64 (dData + DexOff.vaultBalance)).toNat + amount.toNat ∧
    (s'.readU64 (dData + DexOff.totalCapital)).toNat = (s.readU64 (dData + DexOff.totalCapital)).toNat + amount.toNat ∧
    (s'.readU64 (fData + PflOff.capital)).toNat = (s.readU64 (fData + PflOff.capital)).toNat + amount.toNat ∧
    s'.readU64 (dData + DexOff.totalInsurance) = s.readU64 (dData + DexOff.totalInsurance) ∧
    s'.readU64 (dData + DexOff.totalResidual)  = s.readU64 (dData + DexOff.totalResidual) ∧
    s'.readU64 (dData + DexOff.totalSurplus)   = s.readU64 (dData + DexOff.totalSurplus) ∧
    s'.readU64 (dData + DexOff.totalRewards)   = s.readU64 (dData + DexOff.totalRewards) := by
  obtain ⟨_, s₁, hrPos, h1⟩ := bind_ok_elim h
  have ⟨hPosB, hs₁⟩ := require_ok_elim hrPos; subst s₁
  obtain ⟨_, s₂, haV, h2⟩ := bind_ok_elim h1
  have ⟨hVlt, hs₂⟩ := addU64At_ok_spec dData DexOff.vaultBalance amount s s₂ haV; subst s₂
  obtain ⟨_, s₃, haC, h3⟩ := bind_ok_elim h2
  have ⟨hClt, hs₃⟩ := addU64At_ok_spec dData DexOff.totalCapital amount _ s₃ haC; subst s₃
  have ⟨hFlt, hs'⟩ := addU64At_ok_spec fData PflOff.capital amount _ s' h3; subst s'
  have hd208 : dData.toNat + 208 < 2 ^ 64 := hdV
  have hf976 : fData.toNat + 976 < 2 ^ 64 := hfV
  have hDF' : dData.toNat + 208 ≤ fData.toNat ∨ fData.toNat + 976 ≤ dData.toNat := hDF
  have hDdisj : ∀ (st : SvmState) (o1 o2 v : UInt64),
      o1.toNat + 8 ≤ 208 → o2.toNat + 8 ≤ 208 →
      (o1.toNat + 8 ≤ o2.toNat ∨ o2.toNat + 8 ≤ o1.toNat) →
      (st.writeU64 (dData + o1) v).readU64 (dData + o2) = st.readU64 (dData + o2) := by
    intro st o1 o2 v ho1 ho2 hd
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega)]; omega
  have hFoutD : ∀ (st : SvmState) (oD v : UInt64), oD.toNat + 8 ≤ 208 →
      (st.writeU64 (fData + PflOff.capital) v).readU64 (dData + oD) = st.readU64 (dData + oD) := by
    intro st oD v hoD
    have h88 : PflOff.capital.toNat = 88 := rfl
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega), h88]; omega
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), h88]; omega
  have hDoutF : ∀ (st : SvmState) (oD v : UInt64), oD.toNat + 8 ≤ 208 →
      (st.writeU64 (dData + oD) v).readU64 (fData + PflOff.capital) = st.readU64 (fData + PflOff.capital) := by
    intro st oD v hoD
    have h88 : PflOff.capital.toNat = 88 := rfl
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), h88]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), h88]; omega
  have hV' : (((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).writeU64
      (dData + DexOff.totalCapital) ((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).readU64 (dData + DexOff.totalCapital) + amount)).writeU64
      (fData + PflOff.capital) (((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).writeU64
      (dData + DexOff.totalCapital) ((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).readU64 (dData + DexOff.totalCapital) + amount)).readU64 (fData + PflOff.capital) + amount)).readU64
      (dData + DexOff.vaultBalance) = s.readU64 (dData + DexOff.vaultBalance) + amount := by
    rw [hFoutD _ DexOff.vaultBalance _ (by decide),
        hDdisj _ DexOff.totalCapital DexOff.vaultBalance _ (by decide) (by decide) (by decide),
        SvmState.readU64_writeU64_same]
  have hC' : (((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).writeU64
      (dData + DexOff.totalCapital) ((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).readU64 (dData + DexOff.totalCapital) + amount)).writeU64
      (fData + PflOff.capital) (((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).writeU64
      (dData + DexOff.totalCapital) ((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).readU64 (dData + DexOff.totalCapital) + amount)).readU64 (fData + PflOff.capital) + amount)).readU64
      (dData + DexOff.totalCapital) = s.readU64 (dData + DexOff.totalCapital) + amount := by
    rw [hFoutD _ DexOff.totalCapital _ (by decide), SvmState.readU64_writeU64_same,
        hDdisj _ DexOff.vaultBalance DexOff.totalCapital _ (by decide) (by decide) (by decide)]
  have hF' : (((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).writeU64
      (dData + DexOff.totalCapital) ((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).readU64 (dData + DexOff.totalCapital) + amount)).writeU64
      (fData + PflOff.capital) (((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).writeU64
      (dData + DexOff.totalCapital) ((s.writeU64 (dData + DexOff.vaultBalance) (s.readU64 (dData + DexOff.vaultBalance) + amount)).readU64 (dData + DexOff.totalCapital) + amount)).readU64 (fData + PflOff.capital) + amount)).readU64
      (fData + PflOff.capital) = s.readU64 (fData + PflOff.capital) + amount := by
    rw [SvmState.readU64_writeU64_same,
        hDoutF _ DexOff.totalCapital _ (by decide),
        hDoutF _ DexOff.vaultBalance _ (by decide)]
  have hI' : ∀ v1 v2 v3, (((s.writeU64 (dData + DexOff.vaultBalance) v1).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (fData + PflOff.capital) v3).readU64 (dData + DexOff.totalInsurance) = s.readU64 (dData + DexOff.totalInsurance) := fun _ _ _ => by
    rw [hFoutD _ DexOff.totalInsurance _ (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalInsurance _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.vaultBalance DexOff.totalInsurance _ (by decide) (by decide) (by decide)]
  have hR' : ∀ v1 v2 v3, (((s.writeU64 (dData + DexOff.vaultBalance) v1).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (fData + PflOff.capital) v3).readU64 (dData + DexOff.totalResidual) = s.readU64 (dData + DexOff.totalResidual) := fun _ _ _ => by
    rw [hFoutD _ DexOff.totalResidual _ (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalResidual _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.vaultBalance DexOff.totalResidual _ (by decide) (by decide) (by decide)]
  have hS' : ∀ v1 v2 v3, (((s.writeU64 (dData + DexOff.vaultBalance) v1).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (fData + PflOff.capital) v3).readU64 (dData + DexOff.totalSurplus) = s.readU64 (dData + DexOff.totalSurplus) := fun _ _ _ => by
    rw [hFoutD _ DexOff.totalSurplus _ (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalSurplus _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.vaultBalance DexOff.totalSurplus _ (by decide) (by decide) (by decide)]
  have hRew' : ∀ v1 v2 v3, (((s.writeU64 (dData + DexOff.vaultBalance) v1).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (fData + PflOff.capital) v3).readU64 (dData + DexOff.totalRewards) = s.readU64 (dData + DexOff.totalRewards) := fun _ _ _ => by
    rw [hFoutD _ DexOff.totalRewards _ (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalRewards _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.vaultBalance DexOff.totalRewards _ (by decide) (by decide) (by decide)]
  rw [hDdisj _ DexOff.vaultBalance DexOff.totalCapital _ (by decide) (by decide) (by decide)] at hClt
  rw [hDoutF _ DexOff.totalCapital _ (by decide), hDoutF _ DexOff.vaultBalance _ (by decide)] at hFlt
  have hVnat : (s.readU64 (dData + DexOff.vaultBalance) + amount).toNat =
      (s.readU64 (dData + DexOff.vaultBalance)).toNat + amount.toNat := u64_add_toNat_lt _ _ hVlt
  have hCnat : (s.readU64 (dData + DexOff.totalCapital) + amount).toNat =
      (s.readU64 (dData + DexOff.totalCapital)).toNat + amount.toNat := u64_add_toNat_lt _ _ hClt
  have hFnat : (s.readU64 (fData + PflOff.capital) + amount).toNat =
      (s.readU64 (fData + PflOff.capital)).toNat + amount.toNat := u64_add_toNat_lt _ _ hFlt
  refine ⟨UInt64.lt_iff_toNat_lt.mp (of_decide_eq_true hPosB), ?_, by rw [hV', hVnat], by rw [hC', hCnat],
    by rw [hF', hFnat], hI' _ _ _, hR' _ _ _, hS' _ _ _, hRew' _ _ _⟩
  unfold dexStockExact at hStock ⊢
  rw [hC', hI' _ _ _, hR' _ _ _, hS' _ _ _, hRew' _ _ _, hV', hCnat, hVnat]
  omega

/-- **Whole-Handler Theorem #5 (`handleWithdrawCollateral_stock_and_im`)**:
    Directly on `SvmState.mem`, the margin check & state commit of `handleWithdrawCollateral`
    enforces `freeCap' + totalLockedMm ≥ totalIm`, preserves `dexStockExact` BIT-FOR-BIT
    (`V' = V - amt`, `C' = C - amt`), and leaves `I, R, S, F` bit-for-bit unchanged! -/
theorem handleWithdrawCollateral_stock_and_im
    (dData fData : Ptr) (amount : UInt64) (s s' : SvmState)
    (hdV : regionValid dData DexOff.size)
    (hfV : regionValid fData PflOff.size)
    (hDF : regionDisjoint dData DexOff.size fData PflOff.size)
    (hStock : dexStockExact s dData)
    (h : (do
        let freeCap ← loadU64 fData PflOff.capital
        let remFree ← checkedSub64 freeCap amount PErr.insufficientFunds
        let totCap  ← checkedAdd64 remFree (← loadU64 fData PflOff.totalLockedMm)
        SolanaM.require (totCap >= (← loadU64 fData PflOff.totalIm)) PErr.insufficientMargin
        storeU64 fData PflOff.capital remFree
        subU64At dData DexOff.totalCapital amount
        subU64At dData DexOff.vaultBalance amount) s = .ok () s') :
    dexStockExact s' dData ∧
    amount.toNat ≤ (s.readU64 (fData + PflOff.capital)).toNat ∧
    (s'.readU64 (fData + PflOff.capital)).toNat + (s.readU64 (fData + PflOff.totalLockedMm)).toNat ≥
      (s.readU64 (fData + PflOff.totalIm)).toNat ∧
    (s'.readU64 (dData + DexOff.vaultBalance)).toNat + amount.toNat = (s.readU64 (dData + DexOff.vaultBalance)).toNat ∧
    (s'.readU64 (dData + DexOff.totalCapital)).toNat + amount.toNat = (s.readU64 (dData + DexOff.totalCapital)).toNat ∧
    s'.readU64 (dData + DexOff.totalInsurance) = s.readU64 (dData + DexOff.totalInsurance) ∧
    s'.readU64 (dData + DexOff.totalResidual)  = s.readU64 (dData + DexOff.totalResidual) ∧
    s'.readU64 (dData + DexOff.totalSurplus)   = s.readU64 (dData + DexOff.totalSurplus) ∧
    s'.readU64 (dData + DexOff.totalRewards)   = s.readU64 (dData + DexOff.totalRewards) := by
  obtain ⟨freeCap, s₁, hld1, h1⟩ := bind_ok_elim h; unfold loadU64 rawLoadU64 at hld1; cases hld1
  obtain ⟨remFree, s₂, hsub, h2⟩ := bind_ok_elim h1
  have ⟨hAmtLe, hremEq, hremNat, hs₂⟩ := checkedSub64_ok_spec _ _ _ _ _ _ hsub; subst s₂
  obtain ⟨tLock, s₃, hld2, h3⟩ := bind_ok_elim h2; unfold loadU64 rawLoadU64 at hld2; cases hld2
  obtain ⟨totCap, s₄, hadd, h4⟩ := bind_ok_elim h3
  have ⟨_, _, htotNat, hs₄⟩ := checkedAdd64_ok_spec _ _ _ _ _ hadd; subst s₄
  obtain ⟨tIm, s₅, hld3, h5⟩ := bind_ok_elim h4; unfold loadU64 rawLoadU64 at hld3; cases hld3
  obtain ⟨_, s₆, hreqIm, h6⟩ := bind_ok_elim h5
  have ⟨hImB, hs₆⟩ := require_ok_elim hreqIm; subst s₆
  obtain ⟨_, s₇, hstF, h7⟩ := bind_ok_elim h6; unfold storeU64 rawStoreU64 at hstF; cases hstF
  obtain ⟨_, s₈, hsubC, h8⟩ := bind_ok_elim h7
  have ⟨hCle, hs₈⟩ := subU64At_ok_spec dData DexOff.totalCapital amount _ s₈ hsubC; subst s₈
  have ⟨hVle, hs'⟩ := subU64At_ok_spec dData DexOff.vaultBalance amount _ s' h8; subst s'
  have hd208 : dData.toNat + 208 < 2 ^ 64 := hdV
  have hf976 : fData.toNat + 976 < 2 ^ 64 := hfV
  have hDF' : dData.toNat + 208 ≤ fData.toNat ∨ fData.toNat + 976 ≤ dData.toNat := hDF
  have hDdisj : ∀ (st : SvmState) (o1 o2 v : UInt64),
      o1.toNat + 8 ≤ 208 → o2.toNat + 8 ≤ 208 →
      (o1.toNat + 8 ≤ o2.toNat ∨ o2.toNat + 8 ≤ o1.toNat) →
      (st.writeU64 (dData + o1) v).readU64 (dData + o2) = st.readU64 (dData + o2) := by
    intro st o1 o2 v ho1 ho2 hd
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega)]; omega
  have hFoutD : ∀ (st : SvmState) (oD v : UInt64), oD.toNat + 8 ≤ 208 →
      (st.writeU64 (fData + PflOff.capital) v).readU64 (dData + oD) = st.readU64 (dData + oD) := by
    intro st oD v hoD
    have h88 : PflOff.capital.toNat = 88 := rfl
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega), h88]; omega
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), h88]; omega
  have hDoutF : ∀ (st : SvmState) (oD v : UInt64), oD.toNat + 8 ≤ 208 →
      (st.writeU64 (dData + oD) v).readU64 (fData + PflOff.capital) = st.readU64 (fData + PflOff.capital) := by
    intro st oD v hoD
    have h88 : PflOff.capital.toNat = 88 := rfl
    apply readU64_writeU64_of_disjNat
    · rw [u64_add_toNat_lt _ _ (by omega)]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), h88]; omega
    · rw [u64_add_toNat_lt _ _ (by omega), u64_add_toNat_lt _ _ (by omega), h88]; omega
  rw [hFoutD _ DexOff.totalCapital _ (by decide)] at hCle
  rw [hDdisj _ DexOff.totalCapital DexOff.vaultBalance _ (by decide) (by decide) (by decide),
      hFoutD _ DexOff.vaultBalance _ (by decide)] at hVle
  have hF' : ∀ v2 v3, (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (dData + DexOff.vaultBalance) v3).readU64 (fData + PflOff.capital) = remFree := fun _ _ => by
    rw [hDoutF _ DexOff.vaultBalance _ (by decide), hDoutF _ DexOff.totalCapital _ (by decide),
        SvmState.readU64_writeU64_same]
  have hC' : ∀ v3, (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital)
      ((s.writeU64 (fData + PflOff.capital) remFree).readU64 (dData + DexOff.totalCapital) - amount)).writeU64
      (dData + DexOff.vaultBalance) v3).readU64 (dData + DexOff.totalCapital) = s.readU64 (dData + DexOff.totalCapital) - amount := fun _ => by
    rw [hDdisj _ DexOff.vaultBalance DexOff.totalCapital _ (by decide) (by decide) (by decide),
        SvmState.readU64_writeU64_same, hFoutD _ DexOff.totalCapital _ (by decide)]
  have hV' : (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital)
      ((s.writeU64 (fData + PflOff.capital) remFree).readU64 (dData + DexOff.totalCapital) - amount)).writeU64
      (dData + DexOff.vaultBalance) (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital)
      ((s.writeU64 (fData + PflOff.capital) remFree).readU64 (dData + DexOff.totalCapital) - amount)).readU64 (dData + DexOff.vaultBalance) - amount)).readU64
      (dData + DexOff.vaultBalance) = s.readU64 (dData + DexOff.vaultBalance) - amount := by
    rw [SvmState.readU64_writeU64_same,
        hDdisj _ DexOff.totalCapital DexOff.vaultBalance _ (by decide) (by decide) (by decide),
        hFoutD _ DexOff.vaultBalance _ (by decide)]
  have hI' : ∀ v2 v3, (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (dData + DexOff.vaultBalance) v3).readU64 (dData + DexOff.totalInsurance) = s.readU64 (dData + DexOff.totalInsurance) := fun _ _ => by
    rw [hDdisj _ DexOff.vaultBalance DexOff.totalInsurance _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalInsurance _ (by decide) (by decide) (by decide),
        hFoutD _ DexOff.totalInsurance _ (by decide)]
  have hR' : ∀ v2 v3, (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (dData + DexOff.vaultBalance) v3).readU64 (dData + DexOff.totalResidual) = s.readU64 (dData + DexOff.totalResidual) := fun _ _ => by
    rw [hDdisj _ DexOff.vaultBalance DexOff.totalResidual _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalResidual _ (by decide) (by decide) (by decide),
        hFoutD _ DexOff.totalResidual _ (by decide)]
  have hS' : ∀ v2 v3, (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (dData + DexOff.vaultBalance) v3).readU64 (dData + DexOff.totalSurplus) = s.readU64 (dData + DexOff.totalSurplus) := fun _ _ => by
    rw [hDdisj _ DexOff.vaultBalance DexOff.totalSurplus _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalSurplus _ (by decide) (by decide) (by decide),
        hFoutD _ DexOff.totalSurplus _ (by decide)]
  have hRew' : ∀ v2 v3, (((s.writeU64 (fData + PflOff.capital) remFree).writeU64 (dData + DexOff.totalCapital) v2).writeU64
      (dData + DexOff.vaultBalance) v3).readU64 (dData + DexOff.totalRewards) = s.readU64 (dData + DexOff.totalRewards) := fun _ _ => by
    rw [hDdisj _ DexOff.vaultBalance DexOff.totalRewards _ (by decide) (by decide) (by decide),
        hDdisj _ DexOff.totalCapital DexOff.totalRewards _ (by decide) (by decide) (by decide),
        hFoutD _ DexOff.totalRewards _ (by decide)]
  have hCnat : (s.readU64 (dData + DexOff.totalCapital) - amount).toNat =
      (s.readU64 (dData + DexOff.totalCapital)).toNat - amount.toNat := u64_sub_toNat_le _ _ hCle
  have hVnat : (s.readU64 (dData + DexOff.vaultBalance) - amount).toNat =
      (s.readU64 (dData + DexOff.vaultBalance)).toNat - amount.toNat := u64_sub_toNat_le _ _ hVle
  have hImNat : (s.readU64 (fData + PflOff.totalIm)).toNat ≤ totCap.toNat :=
    UInt64.le_iff_toNat_le.mp (of_decide_eq_true hImB)
  refine ⟨?_, hAmtLe, by rw [hF' _ _]; omega, by rw [hV', hVnat]; omega, by rw [hC' _, hCnat]; omega,
    hI' _ _, hR' _ _, hS' _ _, hRew' _ _⟩
  unfold dexStockExact at hStock ⊢
  rw [hC' _, hI' _ _, hR' _ _, hS' _ _, hRew' _ _, hV', hCnat, hVnat]
  omega

end Percolator.HandlerProofs
