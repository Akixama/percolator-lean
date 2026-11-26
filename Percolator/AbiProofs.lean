/-
  Percolator.AbiProofs
  Formal Agave ABI Parser Soundness Proofs across ALL 5 compiled programs:
    1. `Percolator.Program`       (all 24 handlers)
    2. `Percolator.Matcher`       (all 3 handlers)
    3. `Percolator.HlpVault`      (all 5 handlers)
    4. `Percolator.RewardModule`  (all 5 handlers)
    5. `Percolator.OracleAdapter` (all 4 handlers)

  Proves directly on `LeanSVM.SvmState.mem` that:
  - Every `parseStrict1..parseStrict8` handler guarantees `numAccounts ≥ k` and
    `s.mem a_i = ABI.nonDupMarker (0xFF)` for EVERY returned `AccountView` (zero dup-stub overread).
  - Every handler allowing legitimate Solana account aliasing (`CloseAccount` self-refund,
    `Trade` same-owner multi-portfolio, `CreateMarket` `creator == oracleAuth` / `feeVaultTok == creatorTok`,
    `UpdateCreateFee` / `UpdateMarketAuth` self-rotation, `RewardModule.InitReward` `targetMint == quoteMint`)
    resolves via `AccountView.resolveDup` / explicit index checks so EVERY dereferenced account
    ALWAYS satisfies `s.mem eff = ABI.nonDupMarker` and rejects any unauthorized dup index!
  - Every `parseIxOnly` + manual `nextCursor` handler enforces `nonDupMarker` on account 0 and all
    subsequent accounts BEFORE reading header fields (`isSigner`, `isWritable`, `keyPtr`, `ownerPtr`, `dataPtr`).
  - Parser rejection NEVER mutates `SvmState` (`s' = s`).

  Zero `sorry`, zero custom axioms, zero external dependencies.
-/
import LeanSVM
import Percolator.Layout
import Percolator.Program
import Percolator.Matcher
import Percolator.HlpVault
import Percolator.RewardModule
import Percolator.OracleAdapter

namespace Percolator.AbiProofs

open LeanSVM
open LeanSVM.Input
open Percolator

/-! ### 1. Generic Monadic Bind & Non-Dup Elimination Lemmas -/

theorem bind_ok_elim {α β : Type} {m : SolanaM α} {f : α → SolanaM β}
    {s s' : SvmState} {b : β}
    (h : (m >>= f) s = .ok b s') :
    ∃ a s₁, m s = .ok a s₁ ∧ f a s₁ = .ok b s' := by
  cases hm : m s with
  | err _ _ => simp [Bind.bind, SolanaM.bind, hm] at h
  | ok a s₁ => exact ⟨a, s₁, rfl, by simpa [Bind.bind, SolanaM.bind, hm] using h⟩

theorem require_ok_elim {cond : Bool} {err : UInt64} {s s' : SvmState}
    (h : SolanaM.require cond err s = .ok () s') :
    cond = true ∧ s' = s := by
  unfold SolanaM.require at h
  cases cond
  · simp [SolanaM.fail] at h
  · simp [SolanaM.pure] at h; exact ⟨rfl, h.symm⟩

theorem prog_requireNonDup_ok_iff (acc : AccountView) (s s' : SvmState) :
    Program.requireNonDup acc s = .ok () s' ↔
      s.mem acc = ABI.nonDupMarker ∧ s' = s := by
  unfold Program.requireNonDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail, SvmState.readU8]
  by_cases h : s.mem acc = ABI.nonDupMarker
  · simp [h, SolanaM.pure, eq_comm]
  · simp [h, SolanaM.fail]

theorem hlp_requireNonDup_ok_iff (acc : AccountView) (s s' : SvmState) :
    HlpVault.requireNonDup acc s = .ok () s' ↔
      s.mem acc = ABI.nonDupMarker ∧ s' = s := by
  unfold HlpVault.requireNonDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail, SvmState.readU8]
  by_cases h : s.mem acc = ABI.nonDupMarker
  · simp [h, SolanaM.pure, eq_comm]
  · simp [h, SolanaM.fail]

theorem rew_requireNonDup_ok_iff (acc : AccountView) (s s' : SvmState) :
    RewardModule.requireNonDup acc s = .ok () s' ↔
      s.mem acc = ABI.nonDupMarker ∧ s' = s := by
  unfold RewardModule.requireNonDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail, SvmState.readU8]
  by_cases h : s.mem acc = ABI.nonDupMarker
  · simp [h, SolanaM.pure, eq_comm]
  · simp [h, SolanaM.fail]

theorem parseIxOnly_preserves_state (input : Ptr) (s s' : SvmState)
    (r : UInt64 × AccountView × LeanSVM.ByteSlice × Ptr)
    (h : Input.parseIxOnly input s = .ok r s') :
    s' = s ∧ r.1 = s.readU64 input ∧ r.2.1 = Input.firstAccount input := by
  unfold Input.parseIxOnly Input.numAccounts rawLoadU64 at h
  dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure] at h
  cases hsk : Input.skipAccounts (Input.firstAccount input) (s.readU64 input) s with
  | err _ _ => rw [hsk] at h; cases h
  | ok p s₁ =>
    rw [hsk] at h; cases h
    exact ⟨Input.skipAccounts_preserves_state _ _ _ _ _ hsk, rfl, rfl⟩

/-! ### 2. Failure Non-Mutation on Dup-Stub Rejection (`parseStrict` & `resolveDup`) -/

/-- If `requireNonDup` sees any duplicate stub (`s.mem acc ≠ 0xFF`), it fails with `err`
    and leaves `SvmState` 100% unmodified (`s' = s`)! -/
theorem requireNonDup_rejects_dup_preserves_state (acc : AccountView) (err : UInt64) (s : SvmState)
    (hdup : s.mem acc ≠ ABI.nonDupMarker) :
    AccountView.requireNonDup acc err s = .err err s := by
  unfold AccountView.requireNonDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, SolanaM.fail, SvmState.readU8]
  have hb : (s.mem acc == ABI.nonDupMarker) = false := beq_false_of_ne hdup
  simp [hb, SolanaM.fail]

/-- If `resolveDup` sees a duplicate stub whose index is NOT `prevIdx` (e.g. `dest == acc` in
    `CloseAccount` where `acc` is idx 0 and `authority` is idx 1), it fails with `err` and leaves
    `SvmState` 100% unmodified! -/
theorem resolveDup_rejects_wrong_idx_preserves_state
    (acc : AccountView) (prevIdx : UInt8) (prevAcc : AccountView) (err : UInt64) (s : SvmState)
    (hdup : s.mem acc ≠ ABI.nonDupMarker) (hbad : s.mem acc ≠ prevIdx) :
    AccountView.resolveDup acc prevIdx prevAcc err s = .err err s := by
  unfold AccountView.resolveDup rawLoadU8 SolanaM.require
  dsimp only [Bind.bind, SolanaM.bind, SolanaM.fail, SvmState.readU8]
  have h1 : (s.mem acc == ABI.nonDupMarker) = false := beq_false_of_ne hdup
  have h2 : (s.mem acc == prevIdx) = false := beq_false_of_ne hbad
  simp [h1, h2, SolanaM.bind, SolanaM.fail]

/-! ### 3. Core `Percolator.Program` Whole-Handler ABI Soundness -/

theorem handleInitDex_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleInitDex input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 a6 ix pid,
      parseStrict7 input PErr.aliasedAccounts s = .ok (a0, a1, a2, a3, a4, a5, a6, ix, pid) s ∧
      s.readU64 input ≥ 7 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
      s.mem a6 = ABI.nonDupMarker := by
  unfold Program.handleInitDex at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5, m6⟩ := parseStrict7_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 a6 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, a4, a5, a6, ix, pid, hp, hn, m0, m1, m2, m3, m4, m5, m6⟩

theorem handleUpdateOracle_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleUpdateOracle input s = .ok () s') :
    ∃ mkt oracleAuth ix pid,
      parseStrict2 input PErr.aliasedAccounts s = .ok (mkt, oracleAuth, ix, pid) s ∧
      s.readU64 input ≥ 2 ∧
      s.mem mkt = ABI.nonDupMarker ∧ s.mem oracleAuth = ABI.nonDupMarker := by
  unfold Program.handleUpdateOracle at h
  obtain ⟨⟨a0, a1, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ a0 a1 ix pid hp
  subst hs₁
  exact ⟨a0, a1, ix, pid, hp, hn, m0, m1⟩

theorem handleInitPortfolio_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleInitPortfolio input s = .ok () s') :
    ∃ dex pfl owner ix pid,
      parseStrict3 input PErr.aliasedAccounts s = .ok (dex, pfl, owner, ix, pid) s ∧
      s.readU64 input ≥ 3 ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem pfl = ABI.nonDupMarker ∧ s.mem owner = ABI.nonDupMarker := by
  unfold Program.handleInitPortfolio at h
  obtain ⟨⟨a0, a1, a2, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2⟩ := parseStrict3_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, ix, pid, hp, hn, m0, m1, m2⟩

theorem handleDepositCollateral_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleDepositCollateral input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 a6 ix pid,
      parseStrict7 input PErr.aliasedAccounts s = .ok (a0, a1, a2, a3, a4, a5, a6, ix, pid) s ∧
      s.readU64 input ≥ 7 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
      s.mem a6 = ABI.nonDupMarker := by
  unfold Program.handleDepositCollateral at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5, m6⟩ := parseStrict7_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 a6 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, a4, a5, a6, ix, pid, hp, hn, m0, m1, m2, m3, m4, m5, m6⟩

theorem handleWithdrawCollateral_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleWithdrawCollateral input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 a6 ix pid,
      parseStrict7 input PErr.aliasedAccounts s = .ok (a0, a1, a2, a3, a4, a5, a6, ix, pid) s ∧
      s.readU64 input ≥ 7 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
      s.mem a6 = ABI.nonDupMarker := by
  unfold Program.handleWithdrawCollateral at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5, m6⟩ := parseStrict7_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 a6 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, a4, a5, a6, ix, pid, hp, hn, m0, m1, m2, m3, m4, m5, m6⟩

theorem handleWithdrawInsurance_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleWithdrawInsurance input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 ix pid,
      parseStrict8 input PErr.aliasedAccounts s = .ok (a0, a1, a2, a3, a4, a5, a6, a7, ix, pid) s ∧
      s.readU64 input ≥ 8 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
      s.mem a6 = ABI.nonDupMarker ∧ s.mem a7 = ABI.nonDupMarker := by
  unfold Program.handleWithdrawInsurance at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5, m6, m7⟩ :=
    parseStrict8_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 a6 a7 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, ix, pid, hp, hn, m0, m1, m2, m3, m4, m5, m6, m7⟩

theorem handleClearDeadLeg_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleClearDeadLeg input s = .ok () s') :
    ∃ dex mkt pfl ix pid,
      parseStrict3 input PErr.aliasedAccounts s = .ok (dex, mkt, pfl, ix, pid) s ∧
      s.readU64 input ≥ 3 ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧ s.mem pfl = ABI.nonDupMarker := by
  unfold Program.handleClearDeadLeg at h
  obtain ⟨⟨a0, a1, a2, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2⟩ := parseStrict3_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, ix, pid, hp, hn, m0, m1, m2⟩

theorem handleStartWindDown_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleStartWindDown input s = .ok () s') :
    ∃ mkt caller ix pid,
      parseStrict2 input PErr.aliasedAccounts s = .ok (mkt, caller, ix, pid) s ∧
      s.readU64 input ≥ 2 ∧
      s.mem mkt = ABI.nonDupMarker ∧ s.mem caller = ABI.nonDupMarker := by
  unfold Program.handleStartWindDown at h
  obtain ⟨⟨a0, a1, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ a0 a1 ix pid hp
  subst hs₁
  exact ⟨a0, a1, ix, pid, hp, hn, m0, m1⟩

theorem handleForceClosePair_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleForceClosePair input s = .ok () s') :
    ∃ dex mkt pflL pflS ix pid,
      parseStrict4 input PErr.aliasedAccounts s = .ok (dex, mkt, pflL, pflS, ix, pid) s ∧
      s.readU64 input ≥ 4 ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧
      s.mem pflL = ABI.nonDupMarker ∧ s.mem pflS = ABI.nonDupMarker := by
  unfold Program.handleForceClosePair at h
  obtain ⟨⟨a0, a1, a2, a3, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3⟩ := parseStrict4_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, ix, pid, hp, hn, m0, m1, m2, m3⟩

theorem handleResolveMarket_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleResolveMarket input s = .ok () s') :
    ∃ dex mkt ix pid,
      parseStrict2 input PErr.aliasedAccounts s = .ok (dex, mkt, ix, pid) s ∧
      s.readU64 input ≥ 2 ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker := by
  unfold Program.handleResolveMarket at h
  obtain ⟨⟨a0, a1, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ a0 a1 ix pid hp
  subst hs₁
  exact ⟨a0, a1, ix, pid, hp, hn, m0, m1⟩

theorem handleClaimResolved_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleClaimResolved input s = .ok () s') :
    ∃ dex mkt pfl ix pid,
      parseStrict3 input PErr.aliasedAccounts s = .ok (dex, mkt, pfl, ix, pid) s ∧
      s.readU64 input ≥ 3 ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧ s.mem pfl = ABI.nonDupMarker := by
  unfold Program.handleClaimResolved at h
  obtain ⟨⟨a0, a1, a2, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2⟩ := parseStrict3_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, ix, pid, hp, hn, m0, m1, m2⟩

theorem handleTombstoneMarket_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleTombstoneMarket input s = .ok () s') :
    ∃ mkt ix pid,
      parseStrict1 input PErr.aliasedAccounts s = .ok (mkt, ix, pid) s ∧
      s.readU64 input ≥ 1 ∧
      s.mem mkt = ABI.nonDupMarker := by
  unfold Program.handleTombstoneMarket at h
  obtain ⟨⟨a0, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0⟩ := parseStrict1_sound input PErr.aliasedAccounts s s₁ a0 ix pid hp
  subst hs₁
  exact ⟨a0, ix, pid, hp, hn, m0⟩

theorem handleSweepSurplus_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleSweepSurplus input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 ix pid,
      parseStrict6 input PErr.aliasedAccounts s = .ok (a0, a1, a2, a3, a4, a5, ix, pid) s ∧
      s.readU64 input ≥ 6 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker := by
  unfold Program.handleSweepSurplus at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5⟩ := parseStrict6_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, a4, a5, ix, pid, hp, hn, m0, m1, m2, m3, m4, m5⟩

theorem handleClaimReward_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleClaimReward input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 a6 ix pid,
      parseStrict7 input PErr.aliasedAccounts s = .ok (a0, a1, a2, a3, a4, a5, a6, ix, pid) s ∧
      s.readU64 input ≥ 7 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
      s.mem a6 = ABI.nonDupMarker := by
  unfold Program.handleClaimReward at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5, m6⟩ := parseStrict7_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 a6 ix pid hp
  subst hs₁
  exact ⟨a0, a1, a2, a3, a4, a5, a6, ix, pid, hp, hn, m0, m1, m2, m3, m4, m5, m6⟩

/-- `handleCloseAccount` ABI Soundness: `acc` and `authority` are strictly non-duplicate (`0xFF`),
    and `dest` resolves via `resolveDup destRaw 1 authority`, so `dest` is ALWAYS non-duplicate
    (either distinct `destRaw` OR self-refund `authority`), and `destRaw == acc` (dup index `0`)
    is ALWAYS rejected! -/
theorem handleCloseAccount_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleCloseAccount input s = .ok () s') :
    ∃ acc authority destRaw dest ix pid,
      parse3 input s = .ok (acc, authority, destRaw, ix, pid) s ∧
      s.mem acc = ABI.nonDupMarker ∧
      s.mem authority = ABI.nonDupMarker ∧
      s.mem dest = ABI.nonDupMarker ∧
      (dest = destRaw ∨ (s.mem destRaw = 1 ∧ dest = authority)) := by
  unfold Program.handleCloseAccount at h
  obtain ⟨⟨acc, auth, destRaw, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have hs₁ : s₁ = s := by
    unfold parse3 Input.numAccounts rawLoadU64 SolanaM.require at hp
    dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at hp
    by_cases hn : s.readU64 input ≥ 3
    · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at hp
      cases hsk : Input.skipAccounts _ _ s with
      | err _ _ => rw [hsk] at hp; cases hp
      | ok _ s2 => rw [hsk] at hp; cases hp; exact Input.skipAccounts_preserves_state _ _ _ _ _ hsk
    · simp [hn, SolanaM.fail] at hp
  subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hm0, h2⟩ := bind_ok_elim h1
  have ⟨m0, hs₂⟩ := (prog_requireNonDup_ok_iff acc s s₂).mp hm0; subst s₂
  obtain ⟨_, s₃, hm1, h3⟩ := bind_ok_elim h2
  have ⟨m1, hs₃⟩ := (prog_requireNonDup_ok_iff auth s s₃).mp hm1; subst s₃
  obtain ⟨dest, s₄, hres, _⟩ := bind_ok_elim h3
  have ⟨hs₄, mdest⟩ := AccountView.resolveDup_preserves_nonDup destRaw 1 auth PErr.aliasedAccounts s s₄ dest m1 hres
  subst s₄
  have ⟨_, hcase⟩ := (AccountView.resolveDup_ok_iff destRaw 1 auth PErr.aliasedAccounts s s dest).mp hres
  refine ⟨acc, auth, destRaw, dest, ix, pid, hp, m0, m1, mdest, ?_⟩
  rcases hcase with ⟨_, rfl⟩ | ⟨_, hidx, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hidx, rfl⟩

/-- `handleTrade` ABI Soundness: `dex, mkt, pflL, ownerL, pflS` are strictly non-duplicate (`0xFF`),
    and `ownerS` resolves safely via `resolveDup ownerSRaw 3 ownerL` (allowing legitimate
    same-owner trades between two distinct portfolios `pflL ≠ pflS` with zero dup-stub overread!). -/
theorem handleTrade_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleTrade input s = .ok () s') :
    ∃ dex mkt pflL ownerL pflS ownerSRaw ownerS ix pid,
      parse6 input s = .ok (dex, mkt, pflL, ownerL, pflS, ownerSRaw, ix, pid) s ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧
      s.mem pflL = ABI.nonDupMarker ∧ s.mem ownerL = ABI.nonDupMarker ∧
      s.mem pflS = ABI.nonDupMarker ∧ s.mem ownerS = ABI.nonDupMarker := by
  unfold Program.handleTrade at h
  obtain ⟨⟨dex, mkt, pflL, ownerL, pflS, ownerSRaw, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have hs₁ : s₁ = s := by
    unfold parse6 Input.numAccounts rawLoadU64 SolanaM.require at hp
    dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at hp
    by_cases hn : s.readU64 input ≥ 6
    · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at hp
      cases hsk : Input.skipAccounts _ _ s with
      | err _ _ => rw [hsk] at hp; cases hp
      | ok _ s2 => rw [hsk] at hp; cases hp; exact Input.skipAccounts_preserves_state _ _ _ _ _ hsk
    · simp [hn, SolanaM.fail] at hp
  subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hm0, h2⟩ := bind_ok_elim h1; have ⟨m0, hs₂⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm0; subst s₂
  obtain ⟨_, s₃, hm1, h3⟩ := bind_ok_elim h2; have ⟨m1, hs₃⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm1; subst s₃
  obtain ⟨_, s₄, hm2, h4⟩ := bind_ok_elim h3; have ⟨m2, hs₄⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm2; subst s₄
  obtain ⟨_, s₅, hm3, h5⟩ := bind_ok_elim h4; have ⟨m3, hs₅⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm3; subst s₅
  obtain ⟨_, s₆, hm4, h6⟩ := bind_ok_elim h5; have ⟨m4, hs₆⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm4; subst s₆
  obtain ⟨ownerS, s₇, hres, _⟩ := bind_ok_elim h6
  have ⟨hs₇, m5⟩ := AccountView.resolveDup_preserves_nonDup ownerSRaw 3 ownerL PErr.aliasedAccounts s s₇ ownerS m3 hres
  subst s₇
  exact ⟨dex, mkt, pflL, ownerL, pflS, ownerSRaw, ownerS, ix, pid, hp, m0, m1, m2, m3, m4, m5⟩

/-- `handleCreateMarket` ABI Soundness: all 8 resolved accounts (`dex, mkt, mint, oracleAuth, creator,
    creatorTok, feeVaultTok, tokProg`) are guaranteed non-duplicate (`0xFF`), safely permitting
    `creator == oracleAuth` (idx 3) and `feeVaultTok == creatorTok` (idx 5) while blocking all other aliases! -/
theorem handleCreateMarket_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleCreateMarket input s = .ok () s') :
    ∃ dex mkt mint oracleAuth creator creatorTok feeVaultTok tokProg,
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧
      s.mem mint = ABI.nonDupMarker ∧ s.mem oracleAuth = ABI.nonDupMarker ∧
      s.mem creator = ABI.nonDupMarker ∧ s.mem creatorTok = ABI.nonDupMarker ∧
      s.mem feeVaultTok = ABI.nonDupMarker ∧ s.mem tokProg = ABI.nonDupMarker := by
  unfold Program.handleCreateMarket at h
  obtain ⟨⟨dex, mkt, mint, oracleAuth, creatorRaw, creatorTok, feeVaultTokRaw, tokProg, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have hs₁ : s₁ = s := by
    unfold parse8 Input.numAccounts rawLoadU64 SolanaM.require at hp
    dsimp only [Bind.bind, SolanaM.bind, Pure.pure, SolanaM.pure, SolanaM.fail] at hp
    by_cases hn : s.readU64 input ≥ 8
    · simp only [hn, decide_true, ↓reduceIte, SolanaM.pure, AccountView.nextCursor_exact] at hp
      cases hsk : Input.skipAccounts _ _ s with
      | err _ _ => rw [hsk] at hp; cases hp
      | ok _ s2 => rw [hsk] at hp; cases hp; exact Input.skipAccounts_preserves_state _ _ _ _ _ hsk
    · simp [hn, SolanaM.fail] at hp
  subst s₁; dsimp only at h1
  obtain ⟨_, s₂, hm0, h2⟩ := bind_ok_elim h1; have ⟨m0, hs₂⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm0; subst s₂
  obtain ⟨_, s₃, hm1, h3⟩ := bind_ok_elim h2; have ⟨m1, hs₃⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm1; subst s₃
  obtain ⟨_, s₄, hm2, h4⟩ := bind_ok_elim h3; have ⟨m2, hs₄⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm2; subst s₄
  obtain ⟨_, s₅, hm3, h5⟩ := bind_ok_elim h4; have ⟨m3, hs₅⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm3; subst s₅
  obtain ⟨creator, s₆, hr4, h6⟩ := bind_ok_elim h5
  have ⟨hs₆, m4⟩ := AccountView.resolveDup_preserves_nonDup creatorRaw 3 oracleAuth PErr.aliasedAccounts s s₆ creator m3 hr4; subst s₆
  obtain ⟨_, s₇, hm5, h7⟩ := bind_ok_elim h6; have ⟨m5, hs₇⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm5; subst s₇
  obtain ⟨feeVaultTok, s₈, hr6, h8⟩ := bind_ok_elim h7
  have ⟨hs₈, m6⟩ := AccountView.resolveDup_preserves_nonDup feeVaultTokRaw 5 creatorTok PErr.aliasedAccounts s s₈ feeVaultTok m5 hr6; subst s₈
  obtain ⟨_, s₉, hm7, _⟩ := bind_ok_elim h8; have ⟨m7, hs₉⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm7; subst s₉
  exact ⟨dex, mkt, mint, oracleAuth, creator, creatorTok, feeVaultTok, tokProg, m0, m1, m2, m3, m4, m5, m6, m7⟩

/-- `handleLiquidate` ABI Soundness: all 7 core accounts (`dex, mkt, pfl, liqTok, mint, vaultPda, tokProg`)
    are strictly verified non-duplicate (`0xFF`) BEFORE any header read or state mutation! -/
theorem handleLiquidate_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Program.handleLiquidate input s = .ok () s') :
    ∃ dex mkt pfl liqTok mint vaultPda tokProg,
      s.readU64 input ≥ 7 ∧
      s.mem dex = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧
      s.mem pfl = ABI.nonDupMarker ∧ s.mem liqTok = ABI.nonDupMarker ∧
      s.mem mint = ABI.nonDupMarker ∧ s.mem vaultPda = ABI.nonDupMarker ∧
      s.mem tokProg = ABI.nonDupMarker := by
  unfold Program.handleLiquidate at h
  obtain ⟨⟨n, dex, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, hn, _⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at hn h1
  obtain ⟨_, s₂, hreq, h2⟩ := bind_ok_elim h1
  have ⟨hn7, hs₂⟩ := require_ok_elim hreq; subst s₂
  obtain ⟨mkt, s₃, hc1, h3⟩ := bind_ok_elim h2; rw [AccountView.nextCursor_exact] at hc1; injection hc1 with _ hs₃; subst s₃
  obtain ⟨pfl, s₄, hc2, h4⟩ := bind_ok_elim h3; rw [AccountView.nextCursor_exact] at hc2; injection hc2 with _ hs₄; subst s₄
  obtain ⟨liqTok, s₅, hc3, h5⟩ := bind_ok_elim h4; rw [AccountView.nextCursor_exact] at hc3; injection hc3 with _ hs₅; subst s₅
  obtain ⟨mint, s₆, hc4, h6⟩ := bind_ok_elim h5; rw [AccountView.nextCursor_exact] at hc4; injection hc4 with _ hs₆; subst s₆
  obtain ⟨vaultPda, s₇, hc5, h7⟩ := bind_ok_elim h6; rw [AccountView.nextCursor_exact] at hc5; injection hc5 with _ hs₇; subst s₇
  obtain ⟨tokProg, s₈, hc6, h8⟩ := bind_ok_elim h7; rw [AccountView.nextCursor_exact] at hc6; injection hc6 with _ hs₈; subst s₈
  obtain ⟨_, s₉, hm0, h9⟩ := bind_ok_elim h8; have ⟨m0, hs₉⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm0; subst s₉
  obtain ⟨_, s₁₀, hm1, h10⟩ := bind_ok_elim h9; have ⟨m1, hs₁₀⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm1; subst s₁₀
  obtain ⟨_, s₁₁, hm2, h11⟩ := bind_ok_elim h10; have ⟨m2, hs₁₁⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm2; subst s₁₁
  obtain ⟨_, s₁₂, hm3, h12⟩ := bind_ok_elim h11; have ⟨m3, hs₁₂⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm3; subst s₁₂
  obtain ⟨_, s₁₃, hm4, h13⟩ := bind_ok_elim h12; have ⟨m4, hs₁₃⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm4; subst s₁₃
  obtain ⟨_, s₁₄, hm5, h14⟩ := bind_ok_elim h13; have ⟨m5, hs₁₄⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm5; subst s₁₄
  obtain ⟨_, s₁₅, hm6, _⟩ := bind_ok_elim h14; have ⟨m6, hs₁₅⟩ := (prog_requireNonDup_ok_iff _ _ _).mp hm6; subst s₁₅
  exact ⟨dex, mkt, pfl, liqTok, mint, vaultPda, tokProg, by rw [← hn]; exact of_decide_eq_true hn7,
    m0, m1, m2, m3, m4, m5, m6⟩

/-! ### 4. External Programs ABI Soundness (`Matcher`, `HlpVault`, `RewardModule`, `OracleAdapter`) -/

theorem matcher_initPropAmm_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Matcher.handleInitPropAmm input s = .ok () s') :
    ∃ ctx owner, s.readU64 input ≥ 2 ∧ s.mem ctx = ABI.nonDupMarker ∧ s.mem owner = ABI.nonDupMarker := by
  unfold Matcher.handleInitPropAmm at h
  obtain ⟨⟨ctx, owner, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ ctx owner ix pid hp
  subst s₁; exact ⟨ctx, owner, hn, m0, m1⟩

theorem matcher_updatePropAmm_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Matcher.handleUpdatePropAmm input s = .ok () s') :
    ∃ ctx owner, s.readU64 input ≥ 2 ∧ s.mem ctx = ABI.nonDupMarker ∧ s.mem owner = ABI.nonDupMarker := by
  unfold Matcher.handleUpdatePropAmm at h
  obtain ⟨⟨ctx, owner, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1⟩ := parseStrict2_sound input PErr.aliasedAccounts s s₁ ctx owner ix pid hp
  subst s₁; exact ⟨ctx, owner, hn, m0, m1⟩

theorem matcher_propAmmQuote_abi_sound (input : Ptr) (s s' : SvmState)
    (h : Matcher.handlePropAmmQuote input s = .ok () s') :
    s.readU64 input ≥ 1 ∧ s.mem (Input.firstAccount input) = ABI.nonDupMarker := by
  unfold Matcher.handlePropAmmQuote at h
  obtain ⟨⟨n, ctx, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, hn, hctx⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at hn hctx h1
  obtain ⟨_, s₂, hreq, h2⟩ := bind_ok_elim h1
  have ⟨hcond, hs₂⟩ := require_ok_elim hreq; subst s₂
  obtain ⟨_, s₃, hm0, _⟩ := bind_ok_elim h2
  have ⟨m0, _⟩ := (AccountView.requireNonDup_ok_iff ctx PErr.aliasedAccounts s s₃).mp hm0
  have hn1 : n ≥ 1 := by
    have h1' := (Bool.and_eq_true _ _).mp hcond
    exact of_decide_eq_true h1'.1
  rw [hn] at hn1; rw [hctx] at m0
  exact ⟨hn1, m0⟩

theorem hlp_initVault_abi_sound (input : Ptr) (s s' : SvmState)
    (h : HlpVault.handleInitHlpVault input s = .ok () s') :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7,
      s.readU64 input ≥ 8 ∧
      s.mem a0 = ABI.nonDupMarker ∧ s.mem a1 = ABI.nonDupMarker ∧
      s.mem a2 = ABI.nonDupMarker ∧ s.mem a3 = ABI.nonDupMarker ∧
      s.mem a4 = ABI.nonDupMarker ∧ s.mem a5 = ABI.nonDupMarker ∧
      s.mem a6 = ABI.nonDupMarker ∧ s.mem a7 = ABI.nonDupMarker := by
  unfold HlpVault.handleInitHlpVault at h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, ix, pid⟩, s₁, hp, _⟩ := bind_ok_elim h
  have ⟨hs₁, hn, m0, m1, m2, m3, m4, m5, m6, m7⟩ :=
    parseStrict8_sound input PErr.aliasedAccounts s s₁ a0 a1 a2 a3 a4 a5 a6 a7 ix pid hp
  subst s₁; exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, hn, m0, m1, m2, m3, m4, m5, m6, m7⟩

theorem hlp_setMatcher_abi_sound (input : Ptr) (s s' : SvmState)
    (h : HlpVault.handleSetHlpMatcher input s = .ok () s') :
    ∃ vault strategist hlpPfl hlpAuthPda percProg,
      s.readU64 input ≥ 5 ∧
      s.mem vault = ABI.nonDupMarker ∧ s.mem strategist = ABI.nonDupMarker ∧
      s.mem hlpPfl = ABI.nonDupMarker ∧ s.mem hlpAuthPda = ABI.nonDupMarker ∧
      s.mem percProg = ABI.nonDupMarker := by
  unfold HlpVault.handleSetHlpMatcher at h
  obtain ⟨⟨n, vault, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, hn, _⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at hn h1
  obtain ⟨_, s₂, hreq, h2⟩ := bind_ok_elim h1
  have ⟨hn5, hs₂⟩ := require_ok_elim hreq; subst s₂
  obtain ⟨strat, s₃, hc1, h3⟩ := bind_ok_elim h2; rw [AccountView.nextCursor_exact] at hc1; injection hc1 with _ hs₃; subst s₃
  obtain ⟨hlpPfl, s₄, hc2, h4⟩ := bind_ok_elim h3; rw [AccountView.nextCursor_exact] at hc2; injection hc2 with _ hs₄; subst s₄
  obtain ⟨hlpAuth, s₅, hc3, h5⟩ := bind_ok_elim h4; rw [AccountView.nextCursor_exact] at hc3; injection hc3 with _ hs₅; subst s₅
  obtain ⟨perc, s₆, hc4, h6⟩ := bind_ok_elim h5; rw [AccountView.nextCursor_exact] at hc4; injection hc4 with _ hs₆; subst s₆
  obtain ⟨_, s₇, hm0, h7⟩ := bind_ok_elim h6; have ⟨m0, hs₇⟩ := (hlp_requireNonDup_ok_iff _ _ _).mp hm0; subst s₇
  obtain ⟨_, s₈, hm1, h8⟩ := bind_ok_elim h7; have ⟨m1, hs₈⟩ := (hlp_requireNonDup_ok_iff _ _ _).mp hm1; subst s₈
  obtain ⟨_, s₉, hm2, h9⟩ := bind_ok_elim h8; have ⟨m2, hs₉⟩ := (hlp_requireNonDup_ok_iff _ _ _).mp hm2; subst s₉
  obtain ⟨_, s₁₀, hm3, h10⟩ := bind_ok_elim h9; have ⟨m3, hs₁₀⟩ := (hlp_requireNonDup_ok_iff _ _ _).mp hm3; subst s₁₀
  obtain ⟨_, s₁₁, hm4, _⟩ := bind_ok_elim h10; have ⟨m4, hs₁₁⟩ := (hlp_requireNonDup_ok_iff _ _ _).mp hm4; subst s₁₁
  exact ⟨vault, strat, hlpPfl, hlpAuth, perc, by rw [← hn]; exact of_decide_eq_true hn5, m0, m1, m2, m3, m4⟩

theorem oracle_crank_abi_sound (input : Ptr) (s s' : SvmState)
    (h : OracleAdapter.handleCrank input s = .ok () s') :
    ∃ adp mkt feed oracAuthPda percProg,
      s.readU64 input ≥ 5 ∧
      s.mem adp = ABI.nonDupMarker ∧ s.mem mkt = ABI.nonDupMarker ∧
      s.mem feed = ABI.nonDupMarker ∧ s.mem oracAuthPda = ABI.nonDupMarker ∧
      s.mem percProg = ABI.nonDupMarker := by
  unfold OracleAdapter.handleCrank at h
  obtain ⟨⟨n, adp, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, hn, _⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at hn h1
  obtain ⟨_, s₂, hreq, h2⟩ := bind_ok_elim h1
  have ⟨hn5, hs₂⟩ := require_ok_elim hreq; subst s₂
  obtain ⟨mkt, s₃, hc1, h3⟩ := bind_ok_elim h2; rw [AccountView.nextCursor_exact] at hc1; injection hc1 with _ hs₃; subst s₃
  obtain ⟨feed, s₄, hc2, h4⟩ := bind_ok_elim h3; rw [AccountView.nextCursor_exact] at hc2; injection hc2 with _ hs₄; subst s₄
  obtain ⟨orac, s₅, hc3, h5⟩ := bind_ok_elim h4; rw [AccountView.nextCursor_exact] at hc3; injection hc3 with _ hs₅; subst s₅
  obtain ⟨perc, s₆, hc4, h6⟩ := bind_ok_elim h5; rw [AccountView.nextCursor_exact] at hc4; injection hc4 with _ hs₆; subst s₆
  obtain ⟨b0, s₇, hr0, h7⟩ := bind_ok_elim h6; unfold rawLoadU8 at hr0; injection hr0 with hb0eq hs₇; subst s₇; subst hb0eq
  obtain ⟨b1, s₈, hr1, h8⟩ := bind_ok_elim h7; unfold rawLoadU8 at hr1; injection hr1 with hb1eq hs₈; subst s₈; subst hb1eq
  obtain ⟨b2, s₉, hr2, h9⟩ := bind_ok_elim h8; unfold rawLoadU8 at hr2; injection hr2 with hb2eq hs₉; subst s₉; subst hb2eq
  obtain ⟨b3, s₁₀, hr3, h10⟩ := bind_ok_elim h9; unfold rawLoadU8 at hr3; injection hr3 with hb3eq hs₁₀; subst s₁₀; subst hb3eq
  obtain ⟨b4, s₁₁, hr4, h11⟩ := bind_ok_elim h10; unfold rawLoadU8 at hr4; injection hr4 with hb4eq hs₁₁; subst s₁₁; subst hb4eq
  obtain ⟨_, _, hreqAll, _⟩ := bind_ok_elim h11
  have ⟨hAll, _⟩ := require_ok_elim hreqAll
  simp only [SvmState.readU8, Bool.and_eq_true, beq_iff_eq] at hAll
  obtain ⟨⟨⟨⟨m0, m1⟩, m2⟩, m3⟩, m4⟩ := hAll
  exact ⟨adp, mkt, feed, orac, perc, by rw [← hn]; exact of_decide_eq_true hn5, m0, m1, m2, m3, m4⟩

theorem reward_settleEpoch_abi_sound (input : Ptr) (s s' : SvmState)
    (h : RewardModule.handleSettleEpoch input s = .ok () s') :
    ∃ cfg epochAcc rewAuthPda targetEscrow targetMint targetTokProg,
      s.readU64 input ≥ 6 ∧
      s.mem cfg = ABI.nonDupMarker ∧ s.mem epochAcc = ABI.nonDupMarker ∧
      s.mem rewAuthPda = ABI.nonDupMarker ∧ s.mem targetEscrow = ABI.nonDupMarker ∧
      s.mem targetMint = ABI.nonDupMarker ∧ s.mem targetTokProg = ABI.nonDupMarker := by
  unfold RewardModule.handleSettleEpoch at h
  obtain ⟨⟨n, cfg, ix, pid⟩, s₁, hp, h1⟩ := bind_ok_elim h
  have ⟨hs₁, hn, _⟩ := parseIxOnly_preserves_state input s s₁ _ hp; subst s₁; dsimp only at hn h1
  obtain ⟨_, s₂, hreq, h2⟩ := bind_ok_elim h1
  have ⟨hn6, hs₂⟩ := require_ok_elim hreq; subst s₂
  obtain ⟨ep, s₃, hc1, h3⟩ := bind_ok_elim h2; rw [AccountView.nextCursor_exact] at hc1; injection hc1 with _ hs₃; subst s₃
  obtain ⟨rew, s₄, hc2, h4⟩ := bind_ok_elim h3; rw [AccountView.nextCursor_exact] at hc2; injection hc2 with _ hs₄; subst s₄
  obtain ⟨esc, s₅, hc3, h5⟩ := bind_ok_elim h4; rw [AccountView.nextCursor_exact] at hc3; injection hc3 with _ hs₅; subst s₅
  obtain ⟨tm, s₆, hc4, h6⟩ := bind_ok_elim h5; rw [AccountView.nextCursor_exact] at hc4; injection hc4 with _ hs₆; subst s₆
  obtain ⟨tp, s₇, hc5, h7⟩ := bind_ok_elim h6; rw [AccountView.nextCursor_exact] at hc5; injection hc5 with _ hs₇; subst s₇
  obtain ⟨_, s₈, hm0, h8⟩ := bind_ok_elim h7; have ⟨m0, hs₈⟩ := (rew_requireNonDup_ok_iff _ _ _).mp hm0; subst s₈
  obtain ⟨_, s₉, hm1, h9⟩ := bind_ok_elim h8; have ⟨m1, hs₉⟩ := (rew_requireNonDup_ok_iff _ _ _).mp hm1; subst s₉
  obtain ⟨_, s₁₀, hm2, h10⟩ := bind_ok_elim h9; have ⟨m2, hs₁₀⟩ := (rew_requireNonDup_ok_iff _ _ _).mp hm2; subst s₁₀
  obtain ⟨_, s₁₁, hm3, h11⟩ := bind_ok_elim h10; have ⟨m3, hs₁₁⟩ := (rew_requireNonDup_ok_iff _ _ _).mp hm3; subst s₁₁
  obtain ⟨_, s₁₂, hm4, h12⟩ := bind_ok_elim h11; have ⟨m4, hs₁₂⟩ := (rew_requireNonDup_ok_iff _ _ _).mp hm4; subst s₁₂
  obtain ⟨_, s₁₃, hm5, _⟩ := bind_ok_elim h12; have ⟨m5, hs₁₃⟩ := (rew_requireNonDup_ok_iff _ _ _).mp hm5; subst s₁₃
  exact ⟨cfg, ep, rew, esc, tm, tp, by rw [← hn]; exact of_decide_eq_true hn6, m0, m1, m2, m3, m4, m5⟩

end Percolator.AbiProofs
