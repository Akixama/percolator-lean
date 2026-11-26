/-
  Percolator.Proofs
  Machine-checked Lean 4 kernel proofs (0 `sorry`, 0 custom axioms) for `percolator-lean` v2:
  1. Exact Global Stock Equality (`C_tot + I_tot + R_tot + S_tot = V`) across ALL transitions
  2. Cross-Margin Isolation Envelope (BOTH Anti-Reverse-Contagion AND Anti-Shielding!)
  3. Haircut Conservation & Floor-Rounding Monotonicity (No First-Mover Drain)
  4. Derived Side ADL Index Bound (`exposure ≤ OI`) & Zero-Sum Oracle Settlement
  5. Clamped Oracle Solvency Envelope (`stepLoss + liqFee ≤ equity`, 0 bad debt, 0 ins theft)
  6. Finite-Sum Aggregate Bound (`∑ resolvedLegPayout ≤ R_m`, vault can NEVER be over-subscribed!)
  7. Per-Market / Insurance / Untouched-User Isolation, Governance Containment, Termination & Tombstone
-/
import Percolator.Spec

namespace Percolator.Proofs

open Percolator.Spec

private theorem le_mulDivUp_mul (x d : Nat) (hd : 0 < d) :
    x ≤ ((x + d - 1) / d) * d := by
  have h1 := Nat.div_add_mod (x + d - 1) d
  have h2 := Nat.mod_lt (x + d - 1) hd
  rw [Nat.mul_comm] at h1
  omega

theorem updateFn_ne {α β : Type} [DecidableEq α] (f : α → β) (k x : α) (v : β) (hne : x ≠ k) :
    updateFn f k v x = f x := by
  unfold updateFn; simp [hne]

theorem updateFn_eq {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) :
    updateFn f k v k = v := by
  unfold updateFn; simp

/-! ### 1. Haircut Conservation & Monotonicity (INV-4) -/

theorem haircutPayout_le_face (p R P : Nat) : haircutPayout p R P ≤ p := by
  unfold haircutPayout
  split
  · exact Nat.zero_le p
  · next hP =>
    have hPpos : 0 < P := Nat.pos_of_ne_zero hP
    have hdiv := Nat.div_le_div_right (c := P) (Nat.mul_le_mul_left p (Nat.min_le_right R P))
    rwa [Nat.mul_div_cancel p hPpos] at hdiv

theorem haircutPayout_le_residual (p R P : Nat) (hp : p ≤ P) : haircutPayout p R P ≤ R := by
  unfold haircutPayout
  split
  · exact Nat.zero_le R
  · next hP =>
    have hPpos : 0 < P := Nat.pos_of_ne_zero hP
    have h1 : p * min R P ≤ P * R :=
      Nat.le_trans (Nat.mul_le_mul_right (min R P) hp) (Nat.mul_le_mul_left P (Nat.min_le_left R P))
    have h2 := Nat.div_le_div_right (c := P) h1
    rwa [Nat.mul_div_cancel_left R hPpos] at h2

theorem haircutPayout_monotone_ratio (p R P : Nat) (hp : p < P) (hRP : R ≤ P) :
    (R - haircutPayout p R P) * P ≥ R * (P - p) := by
  have hPpos : 0 < P := Nat.lt_of_le_of_lt (Nat.zero_le p) hp
  have hPne : P ≠ 0 := Nat.ne_of_gt hPpos
  have hpay_eq : haircutPayout p R P = (p * R) / P := by
    unfold haircutPayout; simp [hPne, Nat.min_eq_left hRP]
  rw [hpay_eq]
  have hmul_le : ((p * R) / P) * P ≤ p * R := Nat.div_mul_le_self (p * R) P
  rw [Nat.sub_mul, Nat.mul_sub_left_distrib, Nat.mul_comm R p]
  exact Nat.sub_le_sub_left hmul_le (R * P)

/-! ### 2. Finite-Sum Aggregate Payout Bound (Vault Can NEVER Be Over-Subscribed!) -/

/-- Helper lemma: `∑ (a_i * num / den) ≤ (∑ a_i) * num / den` (superadditivity of floor division). -/
theorem sum_mul_div_le (xs : List Nat) (num den : Nat) :
    (xs.map (fun x => (x * num) / den)).sum ≤ (xs.sum * num) / den := by
  induction xs with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.sum_cons]
    by_cases hd : den = 0
    · simp [hd] at ih ⊢; exact ih
    · have hdPos : 0 < den := Nat.pos_of_ne_zero hd
      have hdivAdd : (a * num) / den + (tl.sum * num) / den ≤ (a * num + tl.sum * num) / den := by
        have h1 : ((a * num) / den) * den ≤ a * num := Nat.div_mul_le_self _ _
        have h2 : ((tl.sum * num) / den) * den ≤ tl.sum * num := Nat.div_mul_le_self _ _
        have h3 : ((a * num) / den + (tl.sum * num) / den) * den ≤ a * num + tl.sum * num := by
          rw [Nat.add_mul]; exact Nat.add_le_add h1 h2
        exact (Nat.le_div_iff_mul_le hdPos).mpr h3
      rw [Nat.add_mul]
      exact Nat.le_trans (Nat.add_le_add_left ih _) hdivAdd

/-- INV-15c (Finite-Sum Vault Non-Over-Subscription Theorem):
    For ANY finite list of resolved leg PnLs `pnls` whose sum is `≤ m.resolvedDen`
    (with `m.resolvedNum ≤ m.realizedPool`), the sum of ALL claimants' exact order-independent
    `resolvedLegPayout`s NEVER exceeds `m.realizedPool` (and NEVER exceeds `m.resolvedNum`)! -/
theorem sum_resolved_payouts_le_realizedPool (m : MarketState) (pnls : List Nat)
    (hsum : pnls.sum ≤ m.resolvedDen) (hnum : m.resolvedNum ≤ m.realizedPool) :
    (pnls.map (fun p => resolvedLegPayout m p)).sum ≤ m.realizedPool := by
  unfold resolvedLegPayout
  by_cases hd : m.resolvedDen = 0
  · simp only [hd, ↓reduceIte]
    have hz : (pnls.map (fun _ => 0)).sum = 0 := by clear hsum; induction pnls <;> simp [*]
    omega
  · have hdPos : 0 < m.resolvedDen := Nat.pos_of_ne_zero hd
    simp only [hd, ↓reduceIte]
    calc (pnls.map (fun p => (p * m.resolvedNum) / m.resolvedDen)).sum
        ≤ (pnls.sum * m.resolvedNum) / m.resolvedDen := sum_mul_div_le pnls m.resolvedNum m.resolvedDen
      _ ≤ (m.resolvedDen * m.resolvedNum) / m.resolvedDen :=
          Nat.div_le_div_right (Nat.mul_le_mul_right m.resolvedNum hsum)
      _ = m.resolvedNum := Nat.mul_div_cancel_left m.resolvedNum hdPos
      _ ≤ m.realizedPool := hnum

/-! ### 3. Derived Side ADL Index & Zero-Sum Oracle Settlement (INV-12) -/

theorem deriveAdl_le_one (oi rawBasis : Nat) : deriveAdl oi rawBasis ≤ adlOneNat := by
  unfold deriveAdl
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · next hraw hlt =>
      have hrawPos : 0 < rawBasis := Nat.pos_of_ne_zero hraw
      have hoiLe : oi ≤ rawBasis := Nat.le_of_lt (Nat.lt_of_not_ge hlt)
      calc (adlOneNat * oi) / rawBasis
          ≤ (adlOneNat * rawBasis) / rawBasis := Nat.div_le_div_right (Nat.mul_le_mul_left _ hoiLe)
        _ = adlOneNat := Nat.mul_div_cancel adlOneNat hrawPos

/-- Unconditional Derived Side ADL Exposure Bound (Gap #4A Fix):
    Removing the artificial `max 1` floor-clamp eliminates the unverified `rawBasis ≤ ADL_ONE * oi`
    precondition — `effectiveQty rawBasis (deriveAdl oi rawBasis) ≤ oi` now holds for EVERY `oi ≤ rawBasis`! -/
theorem deriveAdl_exposure_le_oi (oi rawBasis : Nat)
    (hraw : 0 < rawBasis) (hle : oi ≤ rawBasis) :
    effectiveQty rawBasis (deriveAdl oi rawBasis) ≤ oi := by
  unfold effectiveQty deriveAdl
  have hrawNe : rawBasis ≠ 0 := Nat.ne_of_gt hraw
  simp only [hrawNe, ↓reduceIte]
  split
  · next hge =>
    have heq : oi = rawBasis := Nat.le_antisymm hle hge
    subst heq
    have hpos : 0 < adlOneNat := by decide
    rw [Nat.mul_div_cancel oi hpos]
    exact Nat.le_refl _
  · next _ =>
    have hmul : rawBasis * ((adlOneNat * oi) / rawBasis) ≤ adlOneNat * oi := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self (adlOneNat * oi) rawBasis
    have hdiv := Nat.div_le_div_right (c := adlOneNat) hmul
    have hpos : 0 < adlOneNat := by decide
    rwa [Nat.mul_div_cancel_left oi hpos] at hdiv

/-- Zero-Sum Oracle Settlement Theorem: for any price step `diff` and equal `adl` (`adlW ≤ adlL`),
    directional rounding (`gain` floored, `loss` ceiled) guarantees `gain ≤ loss`! -/
theorem oracle_step_zero_sum (adl diff : Nat) :
    mulDivDown adl diff adlOneNat ≤ mulDivUp adl diff adlOneNat := by
  unfold mulDivDown mulDivUp
  have hpos : 0 < adlOneNat := by decide
  simp only [Nat.ne_of_gt hpos, ↓reduceIte]
  exact Nat.div_le_div_right (by omega)

/-! ### 4. Clamped Oracle Solvency Envelope & Cross-Margin Isolation Envelope (THE CORE THEOREM!) -/

theorem oracle_clamp_zero_bad_debt
    (qty oldP newP equity maxMoveBps liqFeeBps mmBps : Nat)
    (henv : maxMoveBps + liqFeeBps ≤ mmBps)
    (hclamp : oracleClampOk oldP newP maxMoveBps)
    (hhealthy : equity ≥ marginReq (marginNotional qty oldP) mmBps) :
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    mulDivDown qty diff posScaleNat + mulDivDown (marginNotional qty oldP) liqFeeBps bpsDenNat ≤ equity := by
  dsimp only
  let diff := if newP ≥ oldP then newP - oldP else oldP - newP
  let N := marginNotional qty oldP
  change mulDivDown qty diff posScaleNat + mulDivDown N liqFeeBps bpsDenNat ≤ equity
  have hposScale : 0 < posScaleNat := by decide
  have hbpsPos : 0 < bpsDenNat := by decide
  have hN : qty * oldP ≤ N * posScaleNat := by
    show qty * oldP ≤ marginNotional qty oldP * posScaleNat
    unfold marginNotional mulDivUp
    simp only [Nat.ne_of_gt hposScale, ↓reduceIte]
    exact le_mulDivUp_mul (qty * oldP) posScaleNat hposScale
  have hstep : mulDivDown qty diff posScaleNat * bpsDenNat ≤ N * maxMoveBps := by
    unfold mulDivDown
    simp only [Nat.ne_of_gt hposScale, ↓reduceIte]
    have h1 : (qty * diff / posScaleNat) * posScaleNat ≤ qty * diff := Nat.div_mul_le_self _ _
    have h2 : (qty * diff / posScaleNat) * bpsDenNat * posScaleNat ≤ N * maxMoveBps * posScaleNat := by
      calc (qty * diff / posScaleNat) * bpsDenNat * posScaleNat
          = (qty * diff / posScaleNat) * posScaleNat * bpsDenNat := by ac_rfl
        _ ≤ (qty * diff) * bpsDenNat := Nat.mul_le_mul_right bpsDenNat h1
        _ = qty * (diff * bpsDenNat) := by ac_rfl
        _ ≤ qty * (oldP * maxMoveBps) := Nat.mul_le_mul_left qty hclamp
        _ = (qty * oldP) * maxMoveBps := by ac_rfl
        _ ≤ (N * posScaleNat) * maxMoveBps := Nat.mul_le_mul_right maxMoveBps hN
        _ = N * maxMoveBps * posScaleNat := by ac_rfl
    exact Nat.le_of_mul_le_mul_right h2 hposScale
  have hliq : mulDivDown N liqFeeBps bpsDenNat * bpsDenNat ≤ N * liqFeeBps := by
    unfold mulDivDown
    simp only [Nat.ne_of_gt hbpsPos, ↓reduceIte]
    exact Nat.div_mul_le_self _ _
  have hcomb : (mulDivDown qty diff posScaleNat + mulDivDown N liqFeeBps bpsDenNat) * bpsDenNat ≤ N * mmBps := by
    calc (mulDivDown qty diff posScaleNat + mulDivDown N liqFeeBps bpsDenNat) * bpsDenNat
        = mulDivDown qty diff posScaleNat * bpsDenNat + mulDivDown N liqFeeBps bpsDenNat * bpsDenNat := Nat.add_mul _ _ _
      _ ≤ N * maxMoveBps + N * liqFeeBps := Nat.add_le_add hstep hliq
      _ = N * (maxMoveBps + liqFeeBps) := (Nat.mul_add N maxMoveBps liqFeeBps).symm
      _ ≤ N * mmBps := Nat.mul_le_mul_left N henv
  have heqBound : N * mmBps ≤ equity * bpsDenNat := by
    have hmm : N * mmBps ≤ marginReq N mmBps * bpsDenNat := by
      unfold marginReq mulDivUp
      simp only [Nat.ne_of_gt hbpsPos, ↓reduceIte]
      exact le_mulDivUp_mul (N * mmBps) bpsDenNat hbpsPos
    exact Nat.le_trans hmm (Nat.mul_le_mul_right bpsDenNat hhealthy)
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans hcomb heqBound) hbpsPos

/-- THE CROSS-MARGIN ISOLATION ENVELOPE THEOREM (Hyperliquid Efficiency + Zero Reverse Contagion + Zero Shielding!):
    1. **Anti-Reverse-Contagion**: Even if a toxic leg (`SCAM`) suffers an arbitrarily huge `loss`
       (e.g. `10^18`), `applyContainedLoss` ALWAYS leaves `capital' ≥ otherMm = totalMm - leg.cachedMm`
       whenever `capital ≥ otherMm` — so unrelated healthy legs (`BTC`) NEVER lose their maintenance margin!
    2. **Anti-Shielding**: Conversely, whenever a portfolio is healthy (`capital ≥ totalMm`, with
       `leg.cachedMm ≤ totalMm` and `leg.cachedMm ≥ marginReq (marginNotional qty oldP) mmBps`),
       NO other leg (even a fake scam leg!) can shield `capital` from paying a healthy market's
       clamped 1-step loss + liquidation fee (`stepLoss + liqFee ≤ capAvailableForLeg capital totalMm leg.cachedMm`)! -/
theorem cross_margin_isolation_envelope
    (capital totalMm qty oldP newP maxMoveBps liqFeeBps mmBps loss : Nat) (leg : LegState)
    (hother : capital ≥ totalMm - leg.cachedMm)
    (hlegLe : leg.cachedMm ≤ totalMm)
    (hcapHealthy : capital ≥ totalMm)
    (hlegMm : leg.cachedMm ≥ marginReq (marginNotional qty oldP) mmBps)
    (henv : maxMoveBps + liqFeeBps ≤ mmBps)
    (hclamp : oracleClampOk oldP newP maxMoveBps) :
    -- 1. Anti-Reverse-Contagion (toxic leg cannot drain `otherMm`):
    (applyContainedLoss capital totalMm leg loss).1 ≥ totalMm - leg.cachedMm ∧
    -- 2. Anti-Shielding (fake legs cannot block healthy market's 1-step loss + liqFee):
    (let diff := if newP ≥ oldP then newP - oldP else oldP - newP
     mulDivDown qty diff posScaleNat + mulDivDown (marginNotional qty oldP) liqFeeBps bpsDenNat
       ≤ capAvailableForLeg capital totalMm leg.cachedMm) := by
  constructor
  · unfold applyContainedLoss capAvailableForLeg
    dsimp only; omega
  · have havail : capAvailableForLeg capital totalMm leg.cachedMm ≥ marginReq (marginNotional qty oldP) mmBps := by
      unfold capAvailableForLeg; dsimp only; omega
    exact oracle_clamp_zero_bad_debt qty oldP newP (capAvailableForLeg capital totalMm leg.cachedMm)
      maxMoveBps liqFeeBps mmBps henv hclamp havail

/-- Minimum nonzero MM floor (`max minMm (marginReq ...)`) strictly strengthens solvency! -/
theorem minMm_strengthens_solvency
    (qty oldP newP equity maxMoveBps liqFeeBps mmBps minMm : Nat)
    (henv : maxMoveBps + liqFeeBps ≤ mmBps)
    (hclamp : oracleClampOk oldP newP maxMoveBps)
    (hhealthy : equity ≥ max minMm (marginReq (marginNotional qty oldP) mmBps)) :
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    mulDivDown qty diff posScaleNat + mulDivDown (marginNotional qty oldP) liqFeeBps bpsDenNat ≤ equity := by
  exact oracle_clamp_zero_bad_debt qty oldP newP equity maxMoveBps liqFeeBps mmBps henv hclamp
    (Nat.le_trans (Nat.le_max_right _ _) hhealthy)

/-! ### 5. Exact Global Stock Equality (`C_tot + I_tot + R_tot + S_tot = V`) & Isolation Across ALL Transitions -/

theorem admin_updateCreateFee_zero_contagion (st st' : DexState) (signer newFee newAdmin : Nat)
    (h : stepUpdateCreateFee st signer newFee newAdmin = some st') :
    st'.stockExact = st.stockExact ∧
    st'.markets = st.markets ∧
    st'.portfolios = st.portfolios ∧
    st'.insShares = st.insShares := by
  unfold stepUpdateCreateFee at h
  split at h
  · cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

theorem createMarket_sound (st st' : DexState)
    (admin initP exitWin maxStale imBps mmBps liqBps tradeBps maxMove maxIns maxOi curSlot otherMid : Nat)
    (hstock : st.stockExact)
    (h : stepCreateMarket st admin initP exitWin maxStale imBps mmBps liqBps tradeBps maxMove maxIns maxOi curSlot = some st')
    (hne : otherMid ≠ st.nextMarketId) :
    st'.stockExact ∧
    (∀ m', st'.markets st.nextMarketId = some m' → m'.wf) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios = st.portfolios := by
  unfold stepCreateMarket at h
  split at h
  · next hc =>
    cases h
    refine ⟨hstock, ?_, updateFn_ne _ _ _ _ hne, rfl⟩
    intro m' hm'
    dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
    unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid MarketState.solvencyEnvelope
    dsimp only
    rcases hc with ⟨_, hEWMin, hEWMax, hStMin, hStMax, _, hMmIm, hImDen, hEnv, _⟩
    exact ⟨fun _ => ⟨rfl, Nat.zero_le _⟩, ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩,
      hEnv, hMmIm, hImDen, hEWMin, hEWMax, hStMin, hStMax⟩
  · cases h

theorem depositCollateral_sound (st st' : DexState) (pid amount otherPid : Nat)
    (hstock : st.stockExact)
    (h : stepDepositCollateral st pid amount = some st')
    (hneP : otherPid ≠ pid) :
    st'.stockExact ∧
    st'.markets = st.markets ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepDepositCollateral at h
  cases hp : st.portfolios pid with
  | none => simp [hp] at h
  | some pfl =>
    simp [hp] at h
    rcases h with ⟨_, hst⟩; subst hst
    unfold DexState.stockExact at *
    exact ⟨by dsimp only; omega, rfl, updateFn_ne _ _ _ _ hneP⟩

theorem withdrawCollateral_sound (st st' : DexState) (pid amount curSlot otherPid : Nat)
    (hstock : st.stockExact)
    (h : stepWithdrawCollateral st pid amount curSlot = some st')
    (hneP : otherPid ≠ pid) :
    st'.stockExact ∧
    st'.markets = st.markets ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepWithdrawCollateral at h
  cases hp : st.portfolios pid with
  | none => simp [hp] at h
  | some pfl =>
    simp [hp] at h
    rcases h with ⟨⟨_, _, htc, hv, _, _⟩, hst⟩; subst hst
    unfold DexState.stockExact at *
    exact ⟨by dsimp only; omega, rfl, updateFn_ne _ _ _ _ hneP⟩

theorem depositInsurance_sound (st st' : DexState) (mid lp amount otherMid : Nat) (donate : Bool)
    (hstock : st.stockExact)
    (h : stepDepositInsurance st mid lp amount donate = some st')
    (hneM : otherMid ≠ mid) :
    st'.stockExact ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios = st.portfolios := by
  unfold stepDepositInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · split at h
      · cases h
        unfold DexState.stockExact at *
        exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, rfl⟩
      · split at h
        · split at h
          · cases h
          · cases h
            unfold DexState.stockExact at *
            exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, rfl⟩
        · split at h
          · cases h
          · cases h
            unfold DexState.stockExact at *
            exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, rfl⟩
    · cases h

theorem withdrawInsurance_sound (st st' : DexState) (mid lp burnShares otherMid : Nat)
    (hstock : st.stockExact)
    (h : stepWithdrawInsurance st mid lp burnShares = some st')
    (hneM : otherMid ≠ mid) :
    st'.stockExact ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios = st.portfolios := by
  unfold stepWithdrawInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · split at h
      · cases h
      · next hpay =>
        cases h
        unfold DexState.stockExact at *
        exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, rfl⟩
    · cases h

theorem realizeLegPnl_sound (st st' : DexState) (mid pid otherMid otherPid : Nat)
    (hstock : st.stockExact)
    (h : stepRealizeLegPnl st mid pid = some st')
    (hneM : otherMid ≠ mid) (hneP : otherPid ≠ pid) :
    st'.stockExact ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid ∧
    st'.totalInsurance = st.totalInsurance := by
  unfold stepRealizeLegPnl at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    cases hp : st.portfolios pid with
    | none => simp [hm, hp] at h
    | some pfl =>
      cases hl : pfl.legs mid with
      | none => simp [hm, hp, hl] at h
      | some leg =>
        simp [hm, hp, hl] at h
        rcases h with ⟨⟨_, _, hleP, hleR⟩, hst⟩; subst hst
        have hpayLe : haircutPayout leg.posPnl m.realizedPool m.totalPosPnl ≤ m.realizedPool :=
          haircutPayout_le_residual _ _ _ hleP
        unfold DexState.stockExact at *
        exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, updateFn_ne _ _ _ _ hneP, rfl⟩

theorem settleContainedLoss_sound (st st' : DexState) (mid pid loss otherMid otherPid : Nat)
    (hstock : st.stockExact)
    (h : stepSettleContainedLoss st mid pid loss = some st')
    (hneM : otherMid ≠ mid) (hneP : otherPid ≠ pid) :
    st'.stockExact ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepSettleContainedLoss at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    cases hp : st.portfolios pid with
    | none => simp [hm, hp] at h
    | some pfl =>
      cases hl : pfl.legs mid with
      | none => simp [hm, hp, hl] at h
      | some leg =>
        simp only [hm, hp, hl, Bind.bind, Option.bind] at h
        split at h
        · next hc =>
          cases h
          unfold DexState.stockExact at *
          exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, updateFn_ne _ _ _ _ hneP⟩
        · cases h

theorem tradeOpen_sound (st st' : DexState) (mid pidL pidS qty spreadLToS spreadSToL otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepTradeOpen st mid pidL pidS qty spreadLToS spreadSToL = some st')
    (hneM : otherMid ≠ mid) (hneL : otherPid ≠ pidL) (hneS : otherPid ≠ pidS) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepTradeOpen at h
  by_cases heq : pidL = pidS
  · simp [heq] at h
  · simp only [heq, ↓reduceIte] at h
    cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hpL : st.portfolios pidL with
      | none => simp [hm, hpL] at h
      | some pL =>
        cases hpS : st.portfolios pidS with
        | none => simp [hm, hpL, hpS] at h
        | some pS =>
          simp only [hm, hpL, hpS, Bind.bind, Option.bind] at h
          by_cases hc : m.status = .active ∧ qty > 0 ∧
              m.adlLong = adlOneNat ∧ m.adlShort = adlOneNat ∧
              m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
              pL.capital + spreadSToL ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spreadLToS ∧
              pS.capital + spreadLToS ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spreadSToL ∧
              st.totalCapital ≥ 2 * marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
          · simp only [hc, and_self, ↓reduceIte, Option.some.injEq] at h
            subst h
            rcases hc with ⟨hstat, _, _, _, hoiLMax, _, _, _, htc⟩
            have hmWf := hwf m hm
            refine ⟨?_, ?_, updateFn_ne _ _ _ _ hneM, ?_⟩
            · unfold DexState.stockExact at *; dsimp only; omega
            · intro m' hm'
              dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
              rcases hmWf with ⟨hoi, hadl, henv⟩
              have hoiAct := hoi (Or.inl hstat)
              unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid at *
              exact ⟨fun _ => by dsimp only; exact ⟨by omega, hoiLMax⟩,
                     by dsimp only; exact ⟨by omega, by omega, Nat.le_refl _, Nat.le_refl _⟩, henv⟩
            · dsimp only; rw [updateFn_ne _ _ _ _ hneS, updateFn_ne _ _ _ _ hneL]
          · simp only [hc, ↓reduceIte] at h; cases h

theorem tradeReduce_sound (st st' : DexState) (mid pidL pidS qty otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepTradeReduce st mid pidL pidS qty = some st')
    (hneM : otherMid ≠ mid) (hneL : otherPid ≠ pidL) (hneS : otherPid ≠ pidS) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepTradeReduce at h
  split at h
  · cases h
  · cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hpL : st.portfolios pidL with
      | none => simp [hm, hpL] at h
      | some pL =>
        cases hpS : st.portfolios pidS with
        | none => simp [hm, hpL, hpS] at h
        | some pS =>
          cases hlL : pL.legs mid with
          | none => simp [hm, hpL, hpS, hlL] at h
          | some lL =>
            cases hlS : pS.legs mid with
            | none => simp [hm, hpL, hpS, hlS] at h
            | some lS =>
              simp only [hm, hpL, hpS, hlL, hlS, Bind.bind, Option.bind] at h
              split at h
              · next hc =>
                split at h
                · cases h
                · split at h
                  · cases h
                  · next hoiRaw =>
                    cases h
                    have hmWf := hwf m hm
                    refine ⟨hstock, ?_, updateFn_ne _ _ _ _ hneM, ?_⟩
                    · intro m' hm'
                      dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
                      rcases hmWf with ⟨hoi, hadl, henv⟩
                      have hoiCur := hoi hc.1
                      unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid at *
                      exact ⟨fun _ => by dsimp only; exact ⟨by omega, by omega⟩,
                             by dsimp only; exact ⟨by omega, by omega, deriveAdl_le_one _ _, deriveAdl_le_one _ _⟩, henv⟩
                    · dsimp only; rw [updateFn_ne _ _ _ _ hneS, updateFn_ne _ _ _ _ hneL]
              · cases h

theorem liquidate_sound (st st' : DexState) (mid pid liqFeeCap loss otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepLiquidate st mid pid liqFeeCap loss = some st')
    (hneM : otherMid ≠ mid) (hneP : otherPid ≠ pid) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepLiquidate at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    cases hp : st.portfolios pid with
    | none => simp [hm, hp] at h
    | some pfl =>
      cases hl : pfl.legs mid with
      | none => simp [hm, hp, hl] at h
      | some leg =>
        simp only [hm, hp, hl, Bind.bind, Option.bind] at h
        split at h
        · next hc =>
          rcases hc with ⟨hstat, hsideNe, _⟩
          cases hls : leg.side with
          | flat => exact False.elim (hsideNe hls)
          | long =>
            simp only [hls] at h
            split at h
            · next hchk =>
              cases h
              have hmWf := hwf m hm
              rcases hchk with ⟨htc, hv, hins, _, hlongChk, _, _⟩
              have hrl := hlongChk trivial
              refine ⟨?_, ?_, updateFn_ne _ _ _ _ hneM, updateFn_ne _ _ _ _ hneP⟩
              · unfold DexState.stockExact at *; dsimp only; omega
              · intro m' hm'
                dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
                rcases hmWf with ⟨hoi, hadl, henv⟩
                have hoiAct := hoi (Or.inl hstat)
                unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid at *
                exact ⟨fun _ => by dsimp only; exact ⟨by omega, by omega⟩,
                       by dsimp only; exact ⟨hrl.2, by omega, deriveAdl_le_one _ _, deriveAdl_le_one _ _⟩, henv⟩
            · cases h
          | short =>
            simp only [hls] at h
            split at h
            · next hchk =>
              cases h
              have hmWf := hwf m hm
              rcases hchk with ⟨htc, hv, hins, _, _, hshortChk, _⟩
              have hrs := hshortChk trivial
              refine ⟨?_, ?_, updateFn_ne _ _ _ _ hneM, updateFn_ne _ _ _ _ hneP⟩
              · unfold DexState.stockExact at *; dsimp only; omega
              · intro m' hm'
                dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
                rcases hmWf with ⟨hoi, hadl, henv⟩
                have hoiAct := hoi (Or.inl hstat)
                unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid at *
                exact ⟨fun _ => by dsimp only; exact ⟨by omega, by omega⟩,
                       by dsimp only; exact ⟨by omega, hrs.2, deriveAdl_le_one _ _, deriveAdl_le_one _ _⟩, henv⟩
            · cases h
        · cases h

theorem clearDeadLeg_sound (st st' : DexState) (mid pid otherMid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepClearDeadLeg st mid pid = some st') (hneM : otherMid ≠ mid) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf) ∧
    st'.markets otherMid = st.markets otherMid := by
  unfold stepClearDeadLeg at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    cases hp : st.portfolios pid with
    | none => simp [hm, hp] at h
    | some pfl =>
      cases hl : pfl.legs mid with
      | none => simp [hm, hp, hl] at h
      | some leg =>
        simp only [hm, hp, hl, Bind.bind, Option.bind] at h
        split at h
        · cases hls : leg.side with
          | flat => simp [hls] at h
          | long =>
            simp only [hls] at h
            split at h
            · next hc =>
              cases h
              have hmWf := hwf m hm
              refine ⟨hstock, ?_, updateFn_ne _ _ _ _ hneM⟩
              intro m' hm'
              dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
              rcases hmWf with ⟨hoi, hadl, henv⟩
              unfold MarketState.wf MarketState.adlValid at *
              exact ⟨hoi, by dsimp only; exact ⟨by omega, hadl.2.1, deriveAdl_le_one _ _, hadl.2.2.2⟩, henv⟩
            · cases h
          | short =>
            simp only [hls] at h
            split at h
            · next hc =>
              cases h
              have hmWf := hwf m hm
              refine ⟨hstock, ?_, updateFn_ne _ _ _ _ hneM⟩
              intro m' hm'
              dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
              rcases hmWf with ⟨hoi, hadl, henv⟩
              unfold MarketState.wf MarketState.adlValid at *
              exact ⟨hoi, by dsimp only; exact ⟨hadl.1, by omega, hadl.2.2.1, deriveAdl_le_one _ _⟩, henv⟩
            · cases h
        · cases h

theorem forceClosePair_terminates_and_sound (st st' : DexState) (mid pidL pidS curSlot otherMid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepForceClosePair st mid pidL pidS curSlot = some st') (hneM : otherMid ≠ mid) :
    st'.stockExact ∧
    (∀ m m', st.markets mid = some m → st'.markets mid = some m' →
      m'.wf ∧ m'.oiLong < m.oiLong ∧ m'.oiShort < m.oiShort) ∧
    st'.markets otherMid = st.markets otherMid := by
  unfold stepForceClosePair at h
  split at h
  · cases h
  · cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hpL : st.portfolios pidL with
      | none => simp [hm, hpL] at h
      | some pL =>
        cases hpS : st.portfolios pidS with
        | none => simp [hm, hpL, hpS] at h
        | some pS =>
          cases hlL : pL.legs mid with
          | none => simp [hm, hpL, hpS, hlL] at h
          | some lL =>
            cases hlS : pS.legs mid with
            | none => simp [hm, hpL, hpS, hlS] at h
            | some lS =>
              simp only [hm, hpL, hpS, hlL, hlS, Bind.bind, Option.bind] at h
              split at h
              · next hc =>
                split at h
                · cases h
                · next hqNe =>
                  split at h
                  · cases h
                  · split at h
                    · cases h
                    · next hoiRaw =>
                      cases h
                      have hmWf := hwf m hm
                      refine ⟨hstock, ?_, updateFn_ne _ _ _ _ hneM⟩
                      intro m0 m' hm0 hm'
                      cases hm0
                      dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
                      rcases hmWf with ⟨hoi, hadl, henv⟩
                      have hoiW := hoi (Or.inr hc.1)
                      unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid at *
                      refine ⟨⟨fun _ => by dsimp only; exact ⟨by omega, by omega⟩,
                               by dsimp only; exact ⟨by omega, by omega, deriveAdl_le_one _ _, deriveAdl_le_one _ _⟩, henv⟩,
                              by dsimp only; omega, by dsimp only; omega⟩
              · cases h

theorem claimResolved_sound (st st' : DexState) (mid pid otherMid otherPid : Nat)
    (hstock : st.stockExact)
    (h : stepClaimResolved st mid pid = some st')
    (hneM : otherMid ≠ mid) (hneP : otherPid ≠ pid) :
    st'.stockExact ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepClaimResolved at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    cases hp : st.portfolios pid with
    | none => simp [hm, hp] at h
    | some pfl =>
      cases hl : pfl.legs mid with
      | none => simp [hm, hp, hl] at h
      | some leg =>
        simp only [hm, hp, hl, Bind.bind, Option.bind] at h
        split at h
        · next hc =>
          split at h
          · cases h
          · next hpayOk =>
            cases h
            unfold DexState.stockExact at *
            exact ⟨by dsimp only; omega, updateFn_ne _ _ _ _ hneM, updateFn_ne _ _ _ _ hneP⟩
        · cases h

theorem resolved_payout_order_independent (m1 m2 : MarketState) (pnl : Nat)
    (hnum : m1.resolvedNum = m2.resolvedNum) (hden : m1.resolvedDen = m2.resolvedDen) :
    resolvedLegPayout m1 pnl = resolvedLegPayout m2 pnl := by
  unfold resolvedLegPayout; rw [hnum, hden]

theorem updateMarketAuth_zero_contagion (st st' : DexState) (mid signer role newKey otherMid : Nat)
    (h : stepUpdateMarketAuth st mid signer role newKey = some st') (hne : otherMid ≠ mid) :
    st'.stockExact = st.stockExact ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios = st.portfolios ∧
    st'.insShares = st.insShares := by
  unfold stepUpdateMarketAuth at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · split at h
      · cases h; exact ⟨rfl, updateFn_ne _ _ _ _ hne, rfl, rfl⟩
      · split at h
        · cases h; exact ⟨rfl, updateFn_ne _ _ _ _ hne, rfl, rfl⟩
        · cases h
    · cases h

theorem tombstone_rejects_updateMarketAuth (st : DexState) (mid signer role newKey : Nat)
    (m : MarketState) (hm : st.markets mid = some m) (htomb : m.status = .tombstoned) :
    stepUpdateMarketAuth st mid signer role newKey = none := by
  unfold stepUpdateMarketAuth; simp [hm, htomb]

/-! ### 6. Post-ADL Dust-Leg Safety, Fair Gradual Fee, Delegate Containment & Takeover -/

/-- Bug Fix #3 Theorem: Ceiling proportional OI removal ALWAYS preserves `oiSide - eff ≤ rawSide - rawClose`,
    even for 1-atom post-ADL dust legs (eliminating stuck-leg liquidation DoS!). -/
theorem ceil_proportional_preserves_oi_le_raw (rawClose oiSide rawSide : Nat)
    (hOiLe : oiSide ≤ rawSide) (hCloseLe : rawClose ≤ rawSide) :
    oiSide - proportionalOiForRaw rawClose oiSide rawSide ≤ rawSide - rawClose := by
  unfold proportionalOiForRaw
  by_cases h0 : oiSide = 0 ∨ rawSide = 0
  · simp only [h0, ↓reduceIte]; rcases h0 with rfl | rfl <;> omega
  · simp only [h0, ↓reduceIte]
    by_cases heq : oiSide = rawSide
    · simp only [heq, ↓reduceIte]; omega
    · simp only [heq, ↓reduceIte]
      have hrawPos : 0 < rawSide := by omega
      have hceil : rawClose * oiSide ≤ mulDivUp rawClose oiSide rawSide * rawSide := by
        unfold mulDivUp
        simp only [Nat.ne_of_gt hrawPos, ↓reduceIte]
        exact le_mulDivUp_mul (rawClose * oiSide) rawSide hrawPos
      let c := max 1 (mulDivUp rawClose oiSide rawSide)
      have hcGe : mulDivUp rawClose oiSide rawSide ≤ c := Nat.le_max_right _ _
      by_cases hcap : c ≥ oiSide
      · have hmin : min oiSide c = oiSide := Nat.min_eq_left hcap
        change oiSide - min oiSide c ≤ rawSide - rawClose
        rw [hmin]; omega
      · have hmin : min oiSide c = c := Nat.min_eq_right (by omega)
        change oiSide - min oiSide c ≤ rawSide - rawClose
        rw [hmin]
        -- Goal: oiSide - c ≤ rawSide - rawClose. Prove via multiplying by `rawSide > 0`!
        have h1 : (oiSide - c) * rawSide ≤ (rawSide - rawClose) * rawSide := by
          have h2 : rawClose * oiSide ≤ c * rawSide :=
            Nat.le_trans hceil (Nat.mul_le_mul_right rawSide hcGe)
          have h3 : (oiSide - c) * rawSide = oiSide * rawSide - c * rawSide := Nat.sub_mul _ _ _
          have h4 : (rawSide - rawClose) * rawSide = rawSide * rawSide - rawClose * rawSide := Nat.sub_mul _ _ _
          have h5 : rawClose * oiSide ≤ rawClose * rawSide := Nat.mul_le_mul_left rawClose hOiLe
          have h6 : oiSide * rawSide + rawClose * rawSide ≤ rawSide * rawSide + c * rawSide := by
            have hle1 : oiSide * rawClose ≤ oiSide * rawSide := Nat.mul_le_mul_left oiSide hCloseLe
            have ha : rawClose * oiSide + oiSide * (rawSide - rawClose) = oiSide * rawSide := by
              rw [Nat.mul_sub_left_distrib, Nat.mul_comm rawClose oiSide]; omega
            have hb : oiSide * (rawSide - rawClose) ≤ rawSide * (rawSide - rawClose) :=
              Nat.mul_le_mul_right _ hOiLe
            rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib, Nat.mul_comm rawSide rawClose, Nat.mul_comm oiSide rawClose] at hb
            have hrr : rawClose * rawSide ≤ rawSide * rawSide := Nat.mul_le_mul_right rawSide hCloseLe
            omega
          have hcm : c * rawSide ≤ oiSide * rawSide := Nat.mul_le_mul_right rawSide (by omega)
          have hrr : rawClose * rawSide ≤ rawSide * rawSide := Nat.mul_le_mul_right rawSide hCloseLe
          have hsub : oiSide * rawSide - c * rawSide ≤ rawSide * rawSide - rawClose * rawSide := by omega
          rwa [h3, h4]
        exact Nat.le_of_mul_le_mul_right h1 hrawPos

/-- Fair Gradual Liquidation Fee Bound: `gradualLiqFee maxFee deficit ≤ maxFee`,
    so `oracle_clamp_zero_bad_debt` holds unconditionally with gradual deficit-scaled fees! -/
theorem gradualLiqFee_le_max (maxFee deficit : Nat) :
    gradualLiqFee maxFee deficit ≤ maxFee := by
  unfold gradualLiqFee; exact Nat.min_le_left _ _

theorem gradual_liqFee_zero_bad_debt
    (qty oldP newP equity maxMoveBps liqFeeBps mmBps deficit : Nat)
    (henv : maxMoveBps + liqFeeBps ≤ mmBps)
    (hclamp : oracleClampOk oldP newP maxMoveBps)
    (hhealthy : equity ≥ marginReq (marginNotional qty oldP) mmBps) :
    let diff := if newP ≥ oldP then newP - oldP else oldP - newP
    let maxFee := mulDivDown (marginNotional qty oldP) liqFeeBps bpsDenNat
    mulDivDown qty diff posScaleNat + gradualLiqFee maxFee deficit ≤ equity := by
  dsimp only
  have hbase := oracle_clamp_zero_bad_debt qty oldP newP equity maxMoveBps liqFeeBps mmBps henv hclamp hhealthy
  have hfee := gradualLiqFee_le_max (mulDivDown (marginNotional qty oldP) liqFeeBps bpsDenNat) deficit
  dsimp only at hbase
  omega

/-- Delegate Custody Isolation: a non-owner delegate can NEVER withdraw collateral! -/
theorem delegate_cannot_withdraw (st : DexState) (pid signer amount curSlot : Nat)
    (pfl : PortfolioState) (hp : st.portfolios pid = some pfl) (hne : signer ≠ pfl.owner) :
    stepWithdrawCollateralAuth st pid signer amount curSlot = none := by
  unfold stepWithdrawCollateralAuth; simp [hp, hne]

/-- Bug Fix #1 Theorem: `Trade(mode=1)` with bounded `execPrice` spread preserves `stockExact`,
    market well-formedness, AND leaves both portfolios above their `newMm` (zero cross-margin bypass!). -/
theorem tradeReduceWithSpread_preserves_isolation
    (st st' : DexState) (mid pidL pidS qty sLToS sSToL newMmL newMmS otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepTradeReduceWithSpread st mid pidL pidS qty sLToS sSToL newMmL newMmS = some st')
    (hneM : otherMid ≠ mid) (hneL : otherPid ≠ pidL) (hneS : otherPid ≠ pidS) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf) ∧
    (∀ pL', st'.portfolios pidL = some pL' → pL'.capital ≥ newMmL) ∧
    (∀ pS', st'.portfolios pidS = some pS' → pS'.capital ≥ newMmS) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepTradeReduceWithSpread at h
  split at h
  · cases h
  · next hneLS =>
    cases hpL : st.portfolios pidL with
    | none => simp [hpL] at h
    | some pL =>
      cases hpS : st.portfolios pidS with
      | none => simp [hpL, hpS] at h
      | some pS =>
        simp only [hpL, hpS, Bind.bind, Option.bind] at h
        split at h
        · next hchk =>
          cases htr : stepTradeReduce st mid pidL pidS qty with
          | none => simp [htr] at h
          | some st1 =>
            simp only [htr] at h
            cases hpL1 : st1.portfolios pidL with
            | none => simp [hpL1] at h
            | some pL1 =>
              cases hpS1 : st1.portfolios pidS with
              | none => simp [hpL1, hpS1] at h
              | some pS1 =>
                simp only [hpL1, hpS1] at h
                cases h
                have hred := tradeReduce_sound st st1 mid pidL pidS qty otherMid otherPid hstock hwf htr hneM hneL hneS
                refine ⟨hred.1, hred.2.1, ?_, ?_, hred.2.2.1, ?_⟩
                · intro pL' hpL'
                  dsimp only at hpL'
                  rw [updateFn_ne _ _ _ _ hneLS, updateFn_eq] at hpL'
                  cases hpL'; exact hchk.2.2.1
                · intro pS' hpS'
                  dsimp only at hpS'
                  rw [updateFn_eq] at hpS'
                  cases hpS'; exact hchk.2.2.2
                · dsimp only
                  rw [updateFn_ne _ _ _ _ hneS, updateFn_ne _ _ _ _ hneL]
                  exact hred.2.2.2
        · cases h

/-- Fair Liquidation Takeover (HLP / Counterparty Tier Before ADL) Soundness Theorem:
    Preserves `stockExact`, `m'.wf` with ZERO ADL (`adlLong' = ADL_ONE ∧ adlShort' = ADL_ONE`),
    victim anti-reverse-contagion (`capital' ≥ totalMm - leg.cachedMm`), and cross-market isolation! -/
theorem liquidateTakeover_sound
    (st st' : DexState) (mid pid liqPid rawClose liqFeeCap loss otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepLiquidateTakeover st mid pid liqPid rawClose liqFeeCap loss = some st')
    (hneM : otherMid ≠ mid) (hneP : otherPid ≠ pid) (hneLiq : otherPid ≠ liqPid) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf ∧ m'.adlLong = adlOneNat ∧ m'.adlShort = adlOneNat) ∧
    (∀ pfl pfl' leg, st.portfolios pid = some pfl → pfl.legs mid = some leg →
      pfl.capital ≥ pfl.totalMm - leg.cachedMm → st'.portfolios pid = some pfl' →
      pfl'.capital ≥ pfl.totalMm - leg.cachedMm) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepLiquidateTakeover at h
  split at h
  · cases h
  · next hnePL =>
    cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hp : st.portfolios pid with
      | none => simp [hm, hp] at h
      | some pfl =>
        cases hlp : st.portfolios liqPid with
        | none => simp [hm, hp, hlp] at h
        | some liqPfl =>
          cases hl : pfl.legs mid with
          | none => simp [hm, hp, hlp, hl] at h
          | some leg =>
            simp only [hm, hp, hlp, hl, Bind.bind, Option.bind] at h
            split at h
            · next hc =>
              split at h
              · next hchk =>
                cases h
                have hmWf := hwf m hm
                refine ⟨?_, ?_, ?_, updateFn_ne _ _ _ _ hneM, ?_⟩
                · unfold DexState.stockExact at *; dsimp only; omega
                · intro m' hm'
                  dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
                  rcases hmWf with ⟨hoi, hadl, henv⟩
                  exact ⟨⟨hoi, hadl, henv⟩, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
                · intro pfl0 pfl' leg0 hp0 hl0 hother hp'
                  have heqP : pfl = pfl0 := Option.some.inj hp0
                  subst heqP
                  have heqL : leg = leg0 := Option.some.inj (hl.symm.trans hl0)
                  subst heqL
                  simp [updateFn, hnePL] at hp'
                  subst hp'
                  unfold applyContainedLoss capAvailableForLeg; dsimp only; omega
                · dsimp only
                  rw [updateFn_ne _ _ _ _ hneLiq, updateFn_ne _ _ _ _ hneP]
              · cases h
            · cases h

/-! ### 7. Closed Inductive Aggregate-Sum Coherence & Bounded Exit-Liveness (Anti-DoS!) -/

/-- Exact list-sum update lemma for `Nodup` ID lists: changing `f k` from `old` to `new`
    shifts `(ids.map f).sum` by exactly `new - old` (or `old - new`). -/
private theorem sum_map_update_add (ids : List Nat) (f : Nat → Nat) (k delta : Nat)
    (hnd : ids.Nodup) (hmem : k ∈ ids) :
    (ids.map (fun x => if x = k then f k + delta else f x)).sum = (ids.map f).sum + delta := by
  induction ids with
  | nil => cases hmem
  | cons a tl ih =>
    simp only [List.nodup_cons, List.mem_cons] at hnd hmem
    simp only [List.map_cons, List.sum_cons]
    rcases hmem with rfl | htl
    · have hrest : tl.map (fun x => if x = k then f k + delta else f x) = tl.map f := by
        apply List.map_congr_left
        intro x hx
        have hne : x ≠ k := fun h => hnd.1 (h ▸ hx)
        simp [hne]
      simp only [↓reduceIte, hrest]; omega
    · have hne : a ≠ k := fun h => hnd.1 (h ▸ htl)
      simp only [hne, ↓reduceIte]; rw [ih hnd.2 htl]; omega

private theorem sum_map_update_sub (ids : List Nat) (f : Nat → Nat) (k delta : Nat)
    (hnd : ids.Nodup) (hmem : k ∈ ids) (hle : delta ≤ f k) :
    (ids.map (fun x => if x = k then f k - delta else f x)).sum = (ids.map f).sum - delta ∧
    delta ≤ (ids.map f).sum := by
  induction ids with
  | nil => cases hmem
  | cons a tl ih =>
    simp only [List.nodup_cons, List.mem_cons] at hnd hmem
    simp only [List.map_cons, List.sum_cons]
    rcases hmem with rfl | htl
    · have hrest : tl.map (fun x => if x = k then f k - delta else f x) = tl.map f := by
        apply List.map_congr_left
        intro x hx
        have hne : x ≠ k := fun h => hnd.1 (h ▸ hx)
        simp [hne]
      simp only [↓reduceIte, hrest]; omega
    · have hne : a ≠ k := fun h => hnd.1 (h ▸ htl)
      have ⟨h1, h2⟩ := ih hnd.2 htl
      simp only [hne, ↓reduceIte, h1]; omega

/-- Inductive Coherence Preservation: `DepositCollateral` preserves exact `C_tot = ∑ capital`,
    `I_tot = ∑ insurance`, `R_tot = ∑ realizedPool`, AND `C_tot + I_tot + R_tot + S_tot = V`! -/
theorem depositCollateral_preserves_coherent (st st' : DexState) (mids pids : List Nat) (pid amount : Nat)
    (hcoh : st.coherent mids pids) (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepDepositCollateral st pid amount = some st') :
    st'.coherent mids pids := by
  unfold stepDepositCollateral at h
  cases hp : st.portfolios pid with
  | none => simp [hp] at h
  | some pfl =>
    simp [hp] at h
    rcases h with ⟨_, hst⟩; subst hst
    rcases hcoh with ⟨hstock, hC, hI, hR⟩
    refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, hI, hR⟩
    unfold sumCaps at *; dsimp only
    rw [hC]; symm
    have hmap : pids.map (getCap (updateFn st.portfolios pid (some { pfl with capital := pfl.capital + amount }))) =
                pids.map (fun x => if x = pid then getCap st.portfolios pid + amount else getCap st.portfolios x) := by
      apply List.map_congr_left; intro x _
      by_cases hx : x = pid
      · subst hx; simp [getCap, updateFn, hp]
      · simp [getCap, updateFn, hx]
    rw [hmap, sum_map_update_add pids (getCap st.portfolios) pid amount hndP hmemP]

theorem withdrawCollateral_preserves_coherent (st st' : DexState) (mids pids : List Nat) (pid amount curSlot : Nat)
    (hcoh : st.coherent mids pids) (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepWithdrawCollateral st pid amount curSlot = some st') :
    st'.coherent mids pids := by
  unfold stepWithdrawCollateral at h
  cases hp : st.portfolios pid with
  | none => simp [hp] at h
  | some pfl =>
    simp [hp] at h
    rcases h with ⟨⟨_, hcap, htc, hv, _, _⟩, hst⟩; subst hst
    rcases hcoh with ⟨hstock, hC, hI, hR⟩
    refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, hI, hR⟩
    unfold sumCaps at *; dsimp only
    rw [hC]; symm
    have hmap : pids.map (getCap (updateFn st.portfolios pid (some { pfl with capital := pfl.capital - amount }))) =
                pids.map (fun x => if x = pid then getCap st.portfolios pid - amount else getCap st.portfolios x) := by
      apply List.map_congr_left; intro x _
      by_cases hx : x = pid
      · subst hx; simp [getCap, updateFn, hp]
      · simp [getCap, updateFn, hx]
    have hle : amount ≤ getCap st.portfolios pid := by simp [getCap, hp]; exact hcap
    rw [hmap, (sum_map_update_sub pids (getCap st.portfolios) pid amount hndP hmemP hle).1]

theorem realizeLegPnl_preserves_coherent (st st' : DexState) (mids pids : List Nat) (mid pid : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepRealizeLegPnl st mid pid = some st') :
    st'.coherent mids pids := by
  unfold stepRealizeLegPnl at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    cases hp : st.portfolios pid with
    | none => simp [hm, hp] at h
    | some pfl =>
      cases hl : pfl.legs mid with
      | none => simp [hm, hp, hl] at h
      | some leg =>
        simp [hm, hp, hl] at h
        rcases h with ⟨⟨_, _, hleP, hleR⟩, hst⟩; subst hst
        have hpayLe : haircutPayout leg.posPnl m.realizedPool m.totalPosPnl ≤ m.realizedPool :=
          haircutPayout_le_residual _ _ _ hleP
        rcases hcoh with ⟨hstock, hC, hI, hR⟩
        let pay := haircutPayout leg.posPnl m.realizedPool m.totalPosPnl
        refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_⟩
        · unfold sumCaps at *; dsimp only
          rw [hC]; symm
          have hmap : pids.map (getCap (updateFn st.portfolios pid (some { pfl with capital := pfl.capital + pay, legs := updateFn pfl.legs mid (some { leg with posPnl := 0 }) }))) =
                      pids.map (fun x => if x = pid then getCap st.portfolios pid + pay else getCap st.portfolios x) := by
            apply List.map_congr_left; intro x _
            by_cases hx : x = pid
            · subst hx; simp [getCap, updateFn, hp]
            · simp [getCap, updateFn, hx]
          rw [hmap, sum_map_update_add pids (getCap st.portfolios) pid pay hndP hmemP]
        · unfold sumIns at *; dsimp only
          have hmap : mids.map (getIns (updateFn st.markets mid (some { m with realizedPool := m.realizedPool - pay, totalPosPnl := m.totalPosPnl - leg.posPnl }))) =
                      mids.map (getIns st.markets) := by
            apply List.map_congr_left; intro x _
            by_cases hx : x = mid
            · subst hx; simp [getIns, updateFn, hm]
            · simp [getIns, updateFn, hx]
          rw [hmap, hI]
        · unfold sumRes at *; dsimp only
          rw [hR]; symm
          have hmap : mids.map (getRes (updateFn st.markets mid (some { m with realizedPool := m.realizedPool - pay, totalPosPnl := m.totalPosPnl - leg.posPnl }))) =
                      mids.map (fun x => if x = mid then getRes st.markets mid - pay else getRes st.markets x) := by
            apply List.map_congr_left; intro x _
            by_cases hx : x = mid
            · subst hx; simp [getRes, updateFn, hm]
            · simp [getRes, updateFn, hx]
          have hle : pay ≤ getRes st.markets mid := by simp [getRes, hm]; exact hpayLe
          rw [hmap, (sum_map_update_sub mids (getRes st.markets) mid pay hndM hmemM hle).1]

/-- Anti-DoS Exit-Liveness Theorem #1: ANY flat portfolio (`totalIm = 0`, all legs empty)
    in a coherent DEX can unconditionally withdraw `100%` of its `capital > 0` at ANY slot! -/
theorem flat_portfolio_unconditionally_withdrawable
    (st : DexState) (mids pids : List Nat) (pid curSlot : Nat) (pfl : PortfolioState)
    (hcoh : st.coherent mids pids) (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (hp : st.portfolios pid = some pfl)
    (hpos : pfl.capital > 0) (him : pfl.totalIm = 0)
    (hflat : ∀ mid, pfl.legs mid = none) :
    ∃ st', stepWithdrawCollateralAuth st pid pfl.owner pfl.capital curSlot = some st' ∧
           st'.coherent mids pids := by
  rcases hcoh with ⟨hstock, hC, hI, hR⟩
  have hcapLeC : pfl.capital ≤ st.totalCapital := by
    rw [hC]; unfold sumCaps
    exact (sum_map_update_sub pids (getCap st.portfolios) pid pfl.capital hndP hmemP (by simp [getCap, hp])).2
  have hcapLeV : pfl.capital ≤ st.vault := by unfold DexState.stockExact at hstock; omega
  have hw : stepWithdrawCollateral st pid pfl.capital curSlot =
            some { st with vault := st.vault - pfl.capital, totalCapital := st.totalCapital - pfl.capital,
                           portfolios := updateFn st.portfolios pid (some { pfl with capital := 0 }) } := by
    unfold stepWithdrawCollateral
    simp [hp, hpos, hcapLeC, hcapLeV, him, hflat, legFreshAt]
  refine ⟨_, ?_, withdrawCollateral_preserves_coherent st _ mids pids pid pfl.capital curSlot ⟨hstock, hC, hI, hR⟩ hndP hmemP hw⟩
  unfold stepWithdrawCollateralAuth
  simp [hp, hw]

/-- Anti-DoS Exit-Liveness Theorem #2: ANY well-formed market `m` has bounded permissionless
    exit deadlines (`maxStaleness ≤ maxStaleNat`, `exitWindow ≤ maxExitWinNat`), so a dead/hostile
    oracle cannot freeze wind-down or force-close beyond `maxStaleNat + maxExitWinNat + 1` slots! -/
theorem market_bounded_exit_liveness (m : MarketState) (hwf : m.wf) :
    m.maxStaleness ≤ maxStaleNat ∧
    m.exitWindow ≤ maxExitWinNat ∧
    m.maxStaleness + m.exitWindow + 1 ≤ maxStaleNat + maxExitWinNat + 1 := by
  rcases hwf with ⟨_, _, henv⟩
  unfold MarketState.solvencyEnvelope at henv
  omega

/-! ### 8. Fair Cross-Margin Liquidation Freshness (A1), Post-ADL Recovery (A2), and Position Hand-Off (B4) -/

/-- A1 Theorem (Anti-Selective-Liquidation):
    1. If ANY active leg `k < st.nextMarketId` on `pfl` was NOT refreshed in `curSlot`,
       `stepLiquidateChecked` unconditionally REJECTS (`= none`), preventing selective single-leg
       liquidation of a hedged cross-margin portfolio without crediting winning legs!
    2. Once all legs are fresh and `cap1 + pnl1 ≥ totalMm` with `shortfall = 0`, `stepLiquidateChecked`
       also REJECTS (`= none`)! -/
theorem hedged_portfolio_immune_to_selective_liquidation
    (st : DexState) (mid pid curSlot liqFeeCap loss : Nat)
    (pfl : PortfolioState) (leg : LegState)
    (hp : st.portfolios pid = some pfl) (hl : pfl.legs mid = some leg) :
    ((∃ k, k < st.nextMarketId ∧ legFreshAt (pfl.legs k) curSlot = false) →
      stepLiquidateChecked st mid pid curSlot liqFeeCap loss = none) ∧
    (let (cap1, pnl1, _, _, shortfall) := applyContainedLoss pfl.capital pfl.totalMm leg loss
     shortfall = 0 → cap1 + pnl1 ≥ pfl.totalMm →
      stepLiquidateChecked st mid pid curSlot liqFeeCap loss = none) := by
  constructor
  · rintro ⟨k, hk, hstale⟩
    unfold stepLiquidateChecked
    simp only [hp, hl, Bind.bind, Option.bind]
    have hnotAll : (List.range st.nextMarketId).all (fun j => legFreshAt (pfl.legs j) curSlot) = false := by
      rw [List.all_eq_false]
      exact ⟨k, List.mem_range.mpr hk, by simp [hstale]⟩
    simp [hnotAll]
  · intro hsf hhealthy
    unfold stepLiquidateChecked
    simp only [hp, hl, Bind.bind, Option.bind]
    split
    · next hcond =>
      rcases hcond with ⟨_, hbad⟩
      unfold applyContainedLoss at hbad
      dsimp only at hbad
      omega
    · rfl

/-- Helper: `postAdlRawAdd` ALWAYS mints at least `qty` raw basis. -/
theorem postAdlRawAdd_ge_qty (qty oi raw : Nat) :
    qty ≤ postAdlRawAdd qty oi raw := by
  unfold postAdlRawAdd
  split
  · omega
  · exact Nat.le_max_left _ _

/-- A2 Core Monotonicity Theorem: Opening `qty` on a partially-ADL'd side (`0 < oi ≤ raw`)
    by minting `rAdd := postAdlRawAdd qty oi raw`:
    1. Preserves `oi + qty ≤ raw + rAdd` (never creates unbacked OI),
    2. Preserves the exact rational ratio `(oi + qty) * raw ≤ oi * (raw + rAdd)` (NEVER inflates
       any existing holder's effective position!),
    3. Guarantees `deriveAdl (oi + qty) (raw + rAdd) ≤ deriveAdl oi raw`! -/
theorem postAdlOpen_preserves_adl_monotone (qty oi raw : Nat)
    (hoi : 0 < oi) (hle : oi ≤ raw) :
    let rAdd := postAdlRawAdd qty oi raw
    oi + qty ≤ raw + rAdd ∧
    (oi + qty) * raw ≤ oi * (raw + rAdd) ∧
    deriveAdl (oi + qty) (raw + rAdd) ≤ deriveAdl oi raw := by
  dsimp only
  have hge : qty ≤ postAdlRawAdd qty oi raw := postAdlRawAdd_ge_qty qty oi raw
  have hle' : oi + qty ≤ raw + postAdlRawAdd qty oi raw := by omega
  have hrat : (oi + qty) * raw ≤ oi * (raw + postAdlRawAdd qty oi raw) := by
    unfold postAdlRawAdd
    split
    · next hor =>
      rcases hor with rfl | heq
      · omega
      · subst heq; exact Nat.le_of_eq (Nat.mul_comm _ _)
    · have hceil : qty * raw ≤ mulDivUp qty raw oi * oi := by
        unfold mulDivUp
        have hne : oi ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        have hdiv := Nat.div_add_mod (qty * raw + oi - 1) oi
        have hmod : (qty * raw + oi - 1) % oi < oi := Nat.mod_lt _ hoi
        have hcomm : oi * ((qty * raw + oi - 1) / oi) = ((qty * raw + oi - 1) / oi) * oi :=
          Nat.mul_comm _ _
        omega
      have hmax : mulDivUp qty raw oi ≤ max qty (mulDivUp qty raw oi) := Nat.le_max_right _ _
      have hmul : mulDivUp qty raw oi * oi ≤ max qty (mulDivUp qty raw oi) * oi :=
        Nat.mul_le_mul_right oi hmax
      have h1 : (oi + qty) * raw = oi * raw + qty * raw := Nat.add_mul oi qty raw
      have h2 : oi * (raw + max qty (mulDivUp qty raw oi)) = oi * raw + max qty (mulDivUp qty raw oi) * oi := by
        rw [Nat.mul_add, Nat.mul_comm oi (max _ _)]
      omega
  refine ⟨hle', hrat, ?_⟩
  have hrawPos : raw > 0 := by omega
  have hraw'Pos : raw + postAdlRawAdd qty oi raw > 0 := by omega
  by_cases hEq : oi = raw
  · subst hEq
    have h1 : deriveAdl oi oi = adlOneNat := by
      unfold deriveAdl; simp [Nat.ne_of_gt hrawPos]
    rw [h1]
    exact deriveAdl_le_one _ _
  · have hlt : oi < raw := by omega
    have hdivLe : (adlOneNat * (oi + qty)) / (raw + postAdlRawAdd qty oi raw) ≤ (adlOneNat * oi) / raw := by
      let raw' := raw + postAdlRawAdd qty oi raw
      let q := (adlOneNat * oi) / raw
      change (adlOneNat * (oi + qty)) / raw' ≤ q
      rw [Nat.div_le_iff_le_mul_add_pred hraw'Pos]
      have hdm := Nat.div_add_mod (adlOneNat * oi) raw
      have hmod : (adlOneNat * oi) % raw < raw := Nat.mod_lt _ hrawPos
      have hcross : adlOneNat * (oi + qty) * raw ≤ adlOneNat * oi * raw' := by
        calc adlOneNat * (oi + qty) * raw
            = adlOneNat * ((oi + qty) * raw) := Nat.mul_assoc _ _ _
          _ ≤ adlOneNat * (oi * raw') := Nat.mul_le_mul_left _ hrat
          _ = adlOneNat * oi * raw' := (Nat.mul_assoc _ _ _).symm
      have hub : adlOneNat * oi ≤ q * raw + (raw - 1) := by
        have hmul : raw * ((adlOneNat * oi) / raw) = q * raw := Nat.mul_comm _ _
        rw [hmul] at hdm
        omega
      have hmulub : adlOneNat * oi * raw' ≤ (q * raw + (raw - 1)) * raw' :=
        Nat.mul_le_mul_right raw' hub
      have hexp : (q * raw + (raw - 1)) * raw' = q * raw' * raw + (raw - 1) * raw' := by
        rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm raw raw', ← Nat.mul_assoc]
      have hstep3 : (raw - 1) * raw' ≤ (raw' - 1) * raw := by
        have hA : (raw - 1) * raw' + raw' = raw * raw' := by
          calc (raw - 1) * raw' + raw' = (raw - 1 + 1) * raw' := by rw [Nat.add_mul, Nat.one_mul]
            _ = raw * raw' := by rw [Nat.sub_add_cancel hrawPos]
        have hB : (raw' - 1) * raw + raw = raw' * raw := by
          calc (raw' - 1) * raw + raw = (raw' - 1 + 1) * raw := by rw [Nat.add_mul, Nat.one_mul]
            _ = raw' * raw := by rw [Nat.sub_add_cancel hraw'Pos]
        have hC : raw * raw' = raw' * raw := Nat.mul_comm raw raw'
        have hleR : raw ≤ raw' := by omega
        omega
      have hbound : adlOneNat * (oi + qty) * raw ≤ (raw' * q + (raw' - 1)) * raw := by
        have hstep1 : adlOneNat * (oi + qty) * raw ≤ q * raw' * raw + (raw - 1) * raw' := by omega
        have hstep2 : (raw' * q + (raw' - 1)) * raw = q * raw' * raw + (raw' - 1) * raw := by
          rw [Nat.add_mul, Nat.mul_comm raw' q]
        omega
      exact Nat.le_of_mul_le_mul_right hbound hrawPos
    unfold deriveAdl
    have hrawNe : raw ≠ 0 := by omega
    have hraw'Ne : raw + postAdlRawAdd qty oi raw ≠ 0 := by omega
    have hnotge : ¬ (oi ≥ raw) := by omega
    have hnotge' : ¬ (oi + qty ≥ raw + postAdlRawAdd qty oi raw) := by
      intro hge'
      have heq' : oi + qty = raw + postAdlRawAdd qty oi raw := by omega
      rw [heq'] at hrat
      rw [Nat.mul_comm oi _] at hrat
      have : raw ≤ oi := Nat.le_of_mul_le_mul_left hrat hraw'Pos
      omega
    simp only [hrawNe, hraw'Ne, hnotge, hnotge', ↓reduceIte]
    omega

/-- A2 Soundness Theorem (`Trade` mode = 0 Post-ADL Open):
    Preserves `stockExact`, `m'.wf` (including `oiLong' = oiShort' ≤ maxOi` and `adlValid`),
    and cross-market/portfolio isolation! -/
theorem tradeOpenPostAdl_sound
    (st st' : DexState) (mid pidL pidS qty spLS spSL otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepTradeOpenPostAdl st mid pidL pidS qty spLS spSL = some st')
    (hneM : otherMid ≠ mid) (hneL : otherPid ≠ pidL) (hneS : otherPid ≠ pidS) :
    st'.stockExact ∧
    (∀ m', st'.markets mid = some m' → m'.wf) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepTradeOpenPostAdl at h
  split at h
  · cases h
  · cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hpL : st.portfolios pidL with
      | none => simp [hm, hpL] at h
      | some pL =>
        cases hpS : st.portfolios pidS with
        | none => simp [hm, hpL, hpS] at h
        | some pS =>
          simp only [hm, hpL, hpS, Bind.bind, Option.bind] at h
          by_cases hc : m.status = .active ∧ qty > 0 ∧
              (m.rawBasisLong = 0 ∨ m.oiLong > 0) ∧
              (m.rawBasisShort = 0 ∨ m.oiShort > 0) ∧
              m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
              pL.capital + spSL ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spLS ∧
              pS.capital + spLS ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spSL ∧
              st.totalCapital ≥ 2 * marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
          · simp only [hc, and_self, ↓reduceIte, Option.some.injEq] at h
            rcases hc with ⟨hact, _, _, _, hmaxL, _, _, _, htotCap⟩
            subst h
            have hmWf := hwf m hm
            rcases hmWf with ⟨hoi, hadl, henv⟩
            have ⟨hbal, _⟩ := hoi (Or.inl hact)
            rcases hadl with ⟨hleL, hleS, _, _⟩
            refine ⟨?_, ?_, updateFn_ne _ _ _ _ hneM, ?_⟩
            · unfold DexState.stockExact at *; dsimp only; omega
            · intro m' hm'
              dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
              have hgeL := postAdlRawAdd_ge_qty qty m.oiLong m.rawBasisLong
              have hgeS := postAdlRawAdd_ge_qty qty m.oiShort m.rawBasisShort
              refine ⟨fun _ => ⟨by dsimp only; omega, by dsimp only; omega⟩,
                ⟨by dsimp only; omega, by dsimp only; omega, deriveAdl_le_one _ _, deriveAdl_le_one _ _⟩, henv⟩
            · dsimp only
              rw [updateFn_ne _ _ _ _ hneS, updateFn_ne _ _ _ _ hneL]
          · simp only [hc, ↓reduceIte] at h; cases h

/-- B4 Soundness Theorem (`Trade` mode = 2/3 Same-Side Position Hand-Off):
    Preserves `stockExact`, leaves the ENTIRE `MarketState` (`oiLong`, `oiShort`, `rawBasisLong`,
    `rawBasisShort`, `adlLong`, `adlShort`) BIT-FOR-BIT INVARIANT, and leaves all other portfolios untouched! -/
theorem tradeHandoff_sound
    (st st' : DexState) (mid pidSell pidBuy qty spBS spSB otherPid : Nat)
    (hstock : st.stockExact)
    (h : stepTradeHandoff st mid pidSell pidBuy qty spBS spSB = some st')
    (hneSell : otherPid ≠ pidSell) (hneBuy : otherPid ≠ pidBuy) :
    st'.stockExact ∧
    st'.markets = st.markets ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepTradeHandoff at h
  split at h
  · cases h
  · cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hp1 : st.portfolios pidSell with
      | none => simp [hm, hp1] at h
      | some pSell =>
        cases hp2 : st.portfolios pidBuy with
        | none => simp [hm, hp1, hp2] at h
        | some pBuy =>
          cases hl : pSell.legs mid with
          | none => simp [hm, hp1, hp2, hl] at h
          | some lSell =>
            simp only [hm, hp1, hp2, hl, Bind.bind, Option.bind] at h
            split at h
            · by_cases hSide : lSell.side = .long
              · simp only [hSide, ↓reduceIte] at h
                split at h
                · cases h
                · cases h; refine ⟨hstock, rfl, ?_⟩; dsimp only; rw [updateFn_ne _ _ _ _ hneBuy, updateFn_ne _ _ _ _ hneSell]
              · simp only [hSide, ↓reduceIte] at h
                split at h
                · cases h
                · cases h; refine ⟨hstock, rfl, ?_⟩; dsimp only; rw [updateFn_ne _ _ _ _ hneBuy, updateFn_ne _ _ _ _ hneSell]
            · cases h

/-- A2 Takeover Soundness Theorem (`Liquidate` mode = 1 Post-ADL Takeover):
    Even during active partial ADL, transfers `rawClose` within the same side while keeping
    `oiLong`, `oiShort`, `rawBasisLong`, `rawBasisShort`, `adlLong`, `adlShort` BIT-FOR-BIT INVARIANT,
    preserving `stockExact`, `m'.wf`, victim `otherMm` containment, and cross-market isolation! -/
theorem liquidateTakeoverPostAdl_sound
    (st st' : DexState) (mid pid liqPid rawClose liqFeeCap loss otherMid otherPid : Nat)
    (hstock : st.stockExact) (hwf : ∀ m, st.markets mid = some m → m.wf)
    (h : stepLiquidateTakeoverPostAdl st mid pid liqPid rawClose liqFeeCap loss = some st')
    (hneM : otherMid ≠ mid) (hneP : otherPid ≠ pid) (hneLiq : otherPid ≠ liqPid) :
    st'.stockExact ∧
    (∀ m m', st.markets mid = some m → st'.markets mid = some m' →
      m'.wf ∧ m'.oiLong = m.oiLong ∧ m'.oiShort = m.oiShort ∧
      m'.rawBasisLong = m.rawBasisLong ∧ m'.rawBasisShort = m.rawBasisShort ∧
      m'.adlLong = m.adlLong ∧ m'.adlShort = m.adlShort) ∧
    (∀ pfl pfl' leg, st.portfolios pid = some pfl → pfl.legs mid = some leg →
      pfl.capital ≥ pfl.totalMm - leg.cachedMm → st'.portfolios pid = some pfl' →
      pfl'.capital ≥ pfl.totalMm - leg.cachedMm) ∧
    st'.markets otherMid = st.markets otherMid ∧
    st'.portfolios otherPid = st.portfolios otherPid := by
  unfold stepLiquidateTakeoverPostAdl at h
  split at h
  · cases h
  · next hnePL =>
    cases hm : st.markets mid with
    | none => simp [hm] at h
    | some m =>
      cases hp : st.portfolios pid with
      | none => simp [hm, hp] at h
      | some pfl =>
        cases hlp : st.portfolios liqPid with
        | none => simp [hm, hp, hlp] at h
        | some liqPfl =>
          cases hl : pfl.legs mid with
          | none => simp [hm, hp, hlp, hl] at h
          | some leg =>
            simp only [hm, hp, hlp, hl, Bind.bind, Option.bind] at h
            split at h
            · split at h
              · cases h
                have hmWf := hwf m hm
                refine ⟨?_, ?_, ?_, updateFn_ne _ _ _ _ hneM, ?_⟩
                · unfold DexState.stockExact at *; dsimp only; omega
                · intro m0 m' hm0 hm'
                  have heqM : m = m0 := Option.some.inj hm0
                  subst heqM
                  dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
                  rcases hmWf with ⟨hoi, hadl, henv⟩
                  exact ⟨⟨hoi, hadl, henv⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
                · intro pfl0 pfl' leg0 hp0 hl0 hother hp'
                  have heqP : pfl = pfl0 := Option.some.inj hp0
                  subst heqP
                  have heqL : leg = leg0 := Option.some.inj (hl.symm.trans hl0)
                  subst heqL
                  simp [updateFn, hnePL] at hp'
                  subst hp'
                  unfold applyContainedLoss capAvailableForLeg; dsimp only; omega
                · dsimp only
                  rw [updateFn_ne _ _ _ _ hneLiq, updateFn_ne _ _ _ _ hneP]
              · cases h
            · cases h

end Percolator.Proofs
