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
      have hdiv : (adlOneNat * oi) / rawBasis ≤ adlOneNat := by
        calc (adlOneNat * oi) / rawBasis
            ≤ (adlOneNat * rawBasis) / rawBasis := Nat.div_le_div_right (Nat.mul_le_mul_left _ hoiLe)
          _ = adlOneNat := Nat.mul_div_cancel adlOneNat hrawPos
      exact Nat.max_le.mpr ⟨by decide, hdiv⟩

theorem deriveAdl_exposure_le_oi (oi rawBasis : Nat)
    (hraw : 0 < rawBasis) (hle : oi ≤ rawBasis) (hnondeg : rawBasis ≤ adlOneNat * oi) :
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
    have hqPos : 1 ≤ (adlOneNat * oi) / rawBasis :=
      (Nat.le_div_iff_mul_le hraw).mpr (by simpa using hnondeg)
    rw [Nat.max_eq_right hqPos]
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
    exact ⟨fun _ => ⟨rfl, Nat.zero_le _⟩, ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩,
      hc.2.2.2.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.1⟩
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
          simp [hm, hpL, hpS] at h
          rcases h with ⟨⟨hstat, _, _, _, hoiLMax, _, _, _, htc⟩, hst⟩; subst hst
          have hmWf := hwf m hm
          refine ⟨?_, ?_, updateFn_ne _ _ _ _ hneM, ?_⟩
          · unfold DexState.stockExact at *; dsimp only; omega
          · intro m' hm'
            dsimp only at hm'; rw [updateFn_eq] at hm'; cases hm'
            rcases hmWf with ⟨hoi, hadl, henv⟩
            have hoiAct := hoi (Or.inl hstat)
            unfold MarketState.wf MarketState.oiBalanced MarketState.adlValid at *
            exact ⟨fun _ => by dsimp only; exact ⟨by omega, hoiLMax⟩,
                   by dsimp only; exact ⟨by omega, by omega, hadl.2.2.1, hadl.2.2.2⟩, henv⟩
          · dsimp only; rw [updateFn_ne _ _ _ _ hneS, updateFn_ne _ _ _ _ hneL]

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

end Percolator.Proofs
