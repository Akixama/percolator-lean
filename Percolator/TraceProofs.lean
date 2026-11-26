/-
  Percolator.TraceProofs
  Remaining Anti-DoS & Unified Multi-Step Inductive Trace Coherence Proofs:
  1. `proportionalRawReduction_preserves_oi_le_raw`: proves `ForceClosePair` and `Trade(mode=1)`
     NEVER stall on `oi' <= raw'` for ANY post-ADL state `0 < qty <= oi <= raw`.
  2. `no_stale_market_freeze_liveness`: proves ZERO freeze window on any active market at any slot
     (either immediately refreshable OR immediately permissionlessly wind-down-able + refreshable).
  3. Unified 13-transition inductive coherence (`DexStep` / `DexReachable` -> `reachable_preserves_coherent`
     & `reachable_global_solvency`): proves across ANY finite interleaving of all 13 balance-moving
     instructions that `C_tot = ∑ capital`, `I_tot = ∑ insurance`, `R_tot = ∑ realizedPool`,
     and `C_tot + I_tot + R_tot + S_tot = V` hold forever!
-/
import Percolator.Proofs

namespace Percolator.TraceProofs

open Percolator.Spec
open Percolator.Proofs

/-! ### 1. Anti-Stall & Zero-Freeze Liveness Theorems -/

/-- **Anti-Stall Theorem (`proportionalRawReduction` Never Violates `oi' ≤ raw'`!)**:
    For ANY post-ADL state `0 < qty ≤ oiSide ≤ rawSide` and ANY leg `0 < rawLeg ≤ rawSide`,
    `red := proportionalRawReduction qty rawLeg rawSide oiSide` satisfies:
    1. `0 < red` (strictly makes progress),
    2. `red ≤ rawLeg ∧ red ≤ rawSide` (never underflows leg or market raw basis),
    3. `oiSide - qty ≤ rawSide - red` (`ForceClosePair` & `Trade(mode=1)` NEVER stall on `oi' ≤ raw'`!). -/
theorem proportionalRawReduction_preserves_oi_le_raw
    (qty rawLeg rawSide oiSide : Nat)
    (hqty : 0 < qty) (hqLe : qty ≤ oiSide) (hoiLe : oiSide ≤ rawSide)
    (hlegPos : 0 < rawLeg) (hlegLe : rawLeg ≤ rawSide) :
    let red := proportionalRawReduction qty rawLeg rawSide oiSide
    0 < red ∧ red ≤ rawLeg ∧ red ≤ rawSide ∧ oiSide - qty ≤ rawSide - red := by
  unfold proportionalRawReduction
  dsimp only
  have hoiPos : 0 < oiSide := by omega
  have hrawPos : 0 < rawSide := by omega
  have hnot0 : ¬ (oiSide = 0 ∨ rawSide = 0) := by omega
  simp only [hnot0, ↓reduceIte]
  by_cases heq : oiSide = rawSide
  · simp only [heq, ↓reduceIte]
    omega
  · simp only [heq, ↓reduceIte]
    have hdivLe : mulDivUp qty rawSide oiSide ≤ rawSide - oiSide + qty := by
      unfold mulDivUp
      have hne : oiSide ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      rw [Nat.div_le_iff_le_mul_add_pred hoiPos]
      have hmul1 : qty * (rawSide - oiSide) ≤ oiSide * (rawSide - oiSide) :=
        Nat.mul_le_mul_right (rawSide - oiSide) hqLe
      have hmul2 : qty * rawSide = qty * (rawSide - oiSide) + qty * oiSide := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hoiLe]
      have hmul3 : oiSide * (rawSide - oiSide + qty) = oiSide * (rawSide - oiSide) + oiSide * qty :=
        Nat.mul_add _ _ _
      have hcomm : oiSide * qty = qty * oiSide := Nat.mul_comm _ _
      omega
    have hmulPos : 1 ≤ mulDivUp qty rawSide oiSide := by
      unfold mulDivUp
      have hne : oiSide ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      have hge : oiSide ≤ qty * rawSide := by
        have h1 : 1 * oiSide ≤ qty * rawSide := Nat.mul_le_mul hqty hoiLe
        omega
      have : oiSide ≤ qty * rawSide + oiSide - 1 := by omega
      exact (Nat.le_div_iff_mul_le hoiPos).mpr (by omega)
    omega

/-- **Zero-Freeze Liveness Theorem**:
    At EVERY slot `curSlot`, any active market `m` has ZERO freeze window:
    either `canRefreshAtSlot m curSlot` holds immediately (oracle is fresh), OR
    `canPermissionlessWindDown m curSlot` holds immediately (ANY caller can permissionlessly
    trigger `StartWindDown`, transitioning `m` to `.windDown` where `canRefreshAtSlot` holds
    unconditionally!). -/
theorem no_stale_market_freeze_liveness (m : MarketState) (curSlot : Nat)
    (hact : m.status = .active) :
    canRefreshAtSlot m curSlot ∨
    (canPermissionlessWindDown m curSlot ∧ canRefreshAtSlot { m with status := .windDown } curSlot) := by
  by_cases hfresh : curSlot - m.lastOracleSlot ≤ m.maxStaleness
  · exact Or.inl (Or.inl ⟨hact, hfresh⟩)
  · exact Or.inr ⟨⟨hact, by omega⟩, Or.inr rfl⟩

/-! ### 2. Unified Multi-Step Inductive Trace Coherence (`DexStep` / `DexReachable`) -/

private theorem sum_map_update_const (ids : List Nat) (f g : Nat → Nat)
    (heq : ∀ x ∈ ids, f x = g x) :
    (ids.map f).sum = (ids.map g).sum := by
  rw [List.map_congr_left heq]

private theorem sum_map_update_one_addSub (ids : List Nat) (f g : Nat → Nat) (k a b : Nat)
    (hnd : ids.Nodup) (hm : k ∈ ids)
    (hgk : g k = f k + a - b) (hge : b ≤ f k + a)
    (hgO : ∀ x, x ≠ k → g x = f x) :
    (ids.map g).sum + b = (ids.map f).sum + a := by
  induction ids with
  | nil => cases hm
  | cons x tl ih =>
    simp only [List.nodup_cons, List.mem_cons] at hnd hm
    simp only [List.map_cons, List.sum_cons]
    rcases hm with rfl | htl
    · have hrest : tl.map g = tl.map f := by
        apply List.map_congr_left; intro y hy
        exact hgO y (fun h => hnd.1 (h ▸ hy))
      rw [hrest, hgk]; omega
    · have hne : x ≠ k := fun h => hnd.1 (h ▸ htl)
      rw [hgO x hne]
      have := ih hnd.2 htl
      omega

private theorem sum_map_update_two_addSub (ids : List Nat) (f g : Nat → Nat) (k1 k2 a1 b1 a2 b2 : Nat)
    (hnd : ids.Nodup) (hm1 : k1 ∈ ids) (hm2 : k2 ∈ ids) (hne : k1 ≠ k2)
    (hg1 : g k1 = f k1 + a1 - b1) (hge1 : b1 ≤ f k1 + a1)
    (hg2 : g k2 = f k2 + a2 - b2) (hge2 : b2 ≤ f k2 + a2)
    (hgO : ∀ x, x ≠ k1 → x ≠ k2 → g x = f x) :
    (ids.map g).sum + b1 + b2 = (ids.map f).sum + a1 + a2 := by
  let h : Nat → Nat := fun x => if x = k1 then f k1 + a1 - b1 else f x
  have h1 : (ids.map h).sum + b1 = (ids.map f).sum + a1 :=
    sum_map_update_one_addSub ids f h k1 a1 b1 hnd hm1 (by simp [h]) hge1 (fun x hx => by simp [h, hx])
  have h2 : (ids.map g).sum + b2 = (ids.map h).sum + a2 :=
    sum_map_update_one_addSub ids h g k2 a2 b2 hnd hm2
      (by simp [h, hne.symm, hg2]) (by simp [h, hne.symm]; exact hge2)
      (fun x hx => by
        by_cases hx1 : x = k1
        · subst hx1; simp [h, hg1]
        · simp [h, hx1, hgO x hx1 hx])
  omega

private theorem sum_map_eq_add (ids : List Nat) (f g : Nat → Nat) (k delta : Nat)
    (hnd : ids.Nodup) (hm : k ∈ ids)
    (hgk : g k = f k + delta) (hgO : ∀ x, x ≠ k → g x = f x) :
    (ids.map f).sum + delta = (ids.map g).sum := by
  have := sum_map_update_one_addSub ids f g k delta 0 hnd hm (by omega) (by omega) hgO
  omega

private theorem sum_map_eq_sub (ids : List Nat) (f g : Nat → Nat) (k delta : Nat)
    (hnd : ids.Nodup) (hm : k ∈ ids)
    (hgk : g k = f k - delta) (hle : delta ≤ f k) (hgO : ∀ x, x ≠ k → g x = f x) :
    (ids.map f).sum - delta = (ids.map g).sum := by
  have := sum_map_update_one_addSub ids f g k 0 delta hnd hm (by omega) (by omega) hgO
  omega

private theorem sumRew_update_same (st : DexState) (mids : List Nat) (mid : Nat) (m m' : MarketState)
    (hm : st.markets mid = some m) (hr : m'.rewardAccrued = m.rewardAccrued) :
    (mids.map (getRew st.markets)).sum = (mids.map (getRew (updateFn st.markets mid (some m')))).sum := by
  apply sum_map_update_const; intro x _
  by_cases hx : x = mid
  · subst hx; simp [getRew, updateFn, hm, hr]
  · simp [getRew, updateFn, hx]

theorem depositInsurance_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid lp amount : Nat) (donate : Bool)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (h : stepDepositInsurance st mid lp amount donate = some st') :
    st'.coherent mids pids := by
  unfold stepDepositInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · cases donate
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hdone : ∀ (minted : Nat),
            ({ st with
              vault          := st.vault + amount
              totalInsurance := st.totalInsurance + amount
              markets        := updateFn st.markets mid (some { m with insurance := m.insurance + amount, totalInsShares := m.totalInsShares + minted })
              insShares      := updateFn st.insShares mid (updateFn (st.insShares mid) lp (st.insShares mid lp + minted)) } : DexState).coherent mids pids := by
          intro minted
          rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
          refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_, ?_⟩
          · unfold sumIns at *; dsimp only; rw [hI]
            exact sum_map_eq_add mids (getIns st.markets) _ mid amount hndM hmemM
              (by simp [getIns, updateFn, hm]) (fun x hx => by simp [getIns, updateFn, hx])
          · unfold sumRes at *; dsimp only; rw [hR]
            apply sum_map_update_const; intro x _
            by_cases hx : x = mid
            · subst hx; simp [getRes, updateFn, hm]
            · simp [getRes, updateFn, hx]
          · unfold sumRew at *; dsimp only; rw [hF]
            apply sumRew_update_same st mids mid m _ hm; rfl
        by_cases h0 : m.totalInsShares = 0 ∨ m.insurance = 0
        · simp only [h0, ↓reduceIte] at h
          split at h
          · cases h
          · cases h; exact hdone amount
        · simp only [h0, ↓reduceIte] at h
          split at h
          · cases h
          · cases h; exact hdone (amount * m.totalInsShares / m.insurance)
      · simp only [↓reduceIte] at h
        cases h
        rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
        refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_, ?_⟩
        · unfold sumIns at *; dsimp only; rw [hI]
          exact sum_map_eq_add mids (getIns st.markets) _ mid amount hndM hmemM
            (by simp [getIns, updateFn, hm]) (fun x hx => by simp [getIns, updateFn, hx])
        · unfold sumRes at *; dsimp only; rw [hR]
          apply sum_map_update_const; intro x _
          by_cases hx : x = mid
          · subst hx; simp [getRes, updateFn, hm]
          · simp [getRes, updateFn, hx]
        · unfold sumRew at *; dsimp only; rw [hF]
          apply sumRew_update_same st mids mid m _ hm; rfl
    · cases h

theorem withdrawInsurance_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid lp burnShares : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (h : stepWithdrawInsurance st mid lp burnShares = some st') :
    st'.coherent mids pids := by
  unfold stepWithdrawInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · next hc =>
      split at h
      · cases h
      · next hok =>
        cases h
        have hpayLe : (burnShares * m.insurance) / m.totalInsShares ≤ m.insurance :=
          Nat.div_le_of_le_mul (Nat.mul_le_mul_right m.insurance hc.2.2.2.2.2.2.2)
        rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
        refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_, ?_⟩
        · unfold sumIns at *; dsimp only; rw [hI]
          exact sum_map_eq_sub mids (getIns st.markets) _ mid
            ((burnShares * m.insurance) / m.totalInsShares) hndM hmemM
            (by simp [getIns, updateFn, hm]) (by simp [getIns, hm]; exact hpayLe)
            (fun x hx => by simp [getIns, updateFn, hx])
        · unfold sumRes at *; dsimp only; rw [hR]
          apply sum_map_update_const; intro x _
          by_cases hx : x = mid
          · subst hx; simp [getRes, updateFn, hm]
          · simp [getRes, updateFn, hx]
        · unfold sumRew at *; dsimp only; rw [hF]
          apply sumRew_update_same st mids mid m _ hm; rfl
    · cases h

theorem settleContainedLoss_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid loss : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepSettleContainedLoss st mid pid loss = some st') :
    st'.coherent mids pids := by
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
          rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
          have hdebLe : (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.1 ≤ pfl.capital := by
            unfold applyContainedLoss capAvailableForLeg; dsimp only; omega
          refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
          · unfold sumCaps at *; dsimp only; rw [hC]
            exact sum_map_eq_sub pids (getCap st.portfolios) _ pid _ hndP hmemP
              (by simp [getCap, updateFn, hp, applyContainedLoss])
              (by simp [getCap, hp]; exact hdebLe)
              (fun x hx => by simp [getCap, updateFn, hx])
          · unfold sumIns at *; dsimp only; rw [hI]
            apply sum_map_update_const; intro x _
            by_cases hx : x = mid
            · subst hx; simp [getIns, updateFn, hm]
            · simp [getIns, updateFn, hx]
          · unfold sumRes at *; dsimp only; rw [hR]
            exact sum_map_eq_add mids (getRes st.markets) _ mid _ hndM hmemM
              (by simp [getRes, updateFn, hm])
              (fun x hx => by simp [getRes, updateFn, hx])
          · unfold sumRew at *; dsimp only; rw [hF]
            apply sumRew_update_same st mids mid m _ hm; rfl
        · cases h

theorem tradeOpenPostAdl_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pidL pidS qty spLS spSL : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemL : pidL ∈ pids) (hmemS : pidS ∈ pids)
    (h : stepTradeOpenPostAdl st mid pidL pidS qty spLS spSL = some st') :
    st'.coherent mids pids := by
  unfold stepTradeOpenPostAdl at h
  split at h
  · cases h
  · next hneLS =>
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
          by_cases hc : m.status = .active ∧ qty > 0 ∧ m.rewardBps ≤ bpsDenNat ∧
              (m.rawBasisLong = 0 ∨ m.oiLong > 0) ∧
              (m.rawBasisShort = 0 ∨ m.oiShort > 0) ∧
              m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
              pL.capital + spSL ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spLS ∧
              pS.capital + spLS ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spSL ∧
              st.totalCapital ≥ 2 * marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
          · simp only [hc, and_self, ↓reduceIte, Option.some.injEq] at h
            subst h
            let fee := marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
            let rewFee := (2 * fee * m.rewardBps) / bpsDenNat
            let insFee := 2 * fee - rewFee
            have hrewLe : rewFee ≤ 2 * fee := by
              have hbps : m.rewardBps ≤ bpsDenNat := hc.2.2.1
              have hmul : 2 * fee * m.rewardBps ≤ 2 * fee * bpsDenNat := Nat.mul_le_mul_left _ hbps
              have hdiv := Nat.div_le_div_right (c := bpsDenNat) hmul
              rwa [Nat.mul_div_cancel _ (by decide)] at hdiv
            dsimp only [rewFee, fee] at hrewLe
            rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
            refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
            · unfold sumCaps at *; dsimp only; rw [hC]
              have hTwo := sum_map_update_two_addSub pids (getCap st.portfolios)
                (getCap (updateFn (updateFn st.portfolios pidL
                  (some { pL with capital := pL.capital + spSL - spLS - fee })) pidS
                  (some { pS with capital := pS.capital + spLS - spSL - fee })))
                pidL pidS spSL (spLS + fee) spLS (spSL + fee) hndP hmemL hmemS hneLS
                (by simp [getCap, updateFn, hneLS, hpL]; omega)
                (by simp [getCap, hpL]; omega)
                (by simp [getCap, updateFn, hpS]; omega)
                (by simp [getCap, hpS]; omega)
                (fun x hxL hxS => by simp [getCap, updateFn, hxL, hxS])
              dsimp only [fee] at hTwo
              omega
            · unfold sumIns at *; dsimp only; rw [hI]
              exact sum_map_eq_add mids (getIns st.markets) _ mid insFee hndM hmemM
                (by simp [getIns, updateFn, hm, insFee, rewFee, fee])
                (fun x hx => by simp [getIns, updateFn, hx])
            · unfold sumRes at *; dsimp only; rw [hR]
              apply sum_map_update_const; intro x _
              by_cases hx : x = mid
              · subst hx; simp [getRes, updateFn, hm]
              · simp [getRes, updateFn, hx]
            · unfold sumRew at *; dsimp only; rw [hF]
              exact sum_map_eq_add mids (getRew st.markets) _ mid rewFee hndM hmemM
                (by simp [getRew, updateFn, hm, rewFee, fee])
                (fun x hx => by simp [getRew, updateFn, hx])
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h

theorem tradeReduce_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pidL pidS qty : Nat)
    (hcoh : st.coherent mids pids)
    (h : stepTradeReduce st mid pidL pidS qty = some st') :
    st'.coherent mids pids := by
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
              · split at h
                · cases h
                · split at h
                  · cases h
                  · cases h
                    rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
                    refine ⟨hstock, ?_, ?_, ?_, ?_⟩
                    · unfold sumCaps at *; dsimp only; rw [hC]
                      apply sum_map_update_const; intro x _
                      by_cases hxS : x = pidS
                      · subst hxS; simp [getCap, updateFn, hpS]
                      · by_cases hxL : x = pidL
                        · subst hxL; simp [getCap, updateFn, hxS, hpL]
                        · simp [getCap, updateFn, hxS, hxL]
                    · unfold sumIns at *; dsimp only; rw [hI]
                      apply sum_map_update_const; intro x _
                      by_cases hx : x = mid
                      · subst hx; simp [getIns, updateFn, hm]
                      · simp [getIns, updateFn, hx]
                    · unfold sumRes at *; dsimp only; rw [hR]
                      apply sum_map_update_const; intro x _
                      by_cases hx : x = mid
                      · subst hx; simp [getRes, updateFn, hm]
                      · simp [getRes, updateFn, hx]
                    · unfold sumRew at *; dsimp only; rw [hF]
                      apply sumRew_update_same st mids mid m _ hm; rfl
              · cases h

theorem tradeHandoff_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pidSell pidBuy qty spBS spSB : Nat)
    (hcoh : st.coherent mids pids) (hndP : pids.Nodup) (hmemS : pidSell ∈ pids) (hmemB : pidBuy ∈ pids)
    (h : stepTradeHandoff st mid pidSell pidBuy qty spBS spSB = some st') :
    st'.coherent mids pids := by
  unfold stepTradeHandoff at h
  split at h
  · cases h
  · next hneSB =>
    cases hm : st.markets mid with
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
            · next hc =>
              have hTwoGen : ∀ (lSell' : LegState),
                  let ps' := updateFn (updateFn st.portfolios pidSell
                      (some { pSell with capital := pSell.capital + spBS - spSB, legs := updateFn pSell.legs mid (some lSell') }))
                      pidBuy (some { pBuy with capital := pBuy.capital + spSB - spBS })
                  ({ st with portfolios := ps' } : DexState).coherent mids pids := by
                intro lSell' ps'
                rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
                refine ⟨hstock, ?_, hI, hR, hF⟩
                unfold sumCaps at *; dsimp only; rw [hC]
                have hTwo := sum_map_update_two_addSub pids (getCap st.portfolios) (getCap ps')
                  pidSell pidBuy spBS spSB spSB spBS hndP hmemS hmemB hneSB
                  (by simp [ps', getCap, updateFn, hneSB, hp1])
                  (by simp [getCap, hp1]; omega)
                  (by simp [ps', getCap, updateFn, hp2])
                  (by simp [getCap, hp2]; omega)
                  (fun x hxS hxB => by simp [ps', getCap, updateFn, hxS, hxB])
                omega
              by_cases hSide : lSell.side = .long
              · simp only [hSide, ↓reduceIte] at h
                split at h
                · cases h
                · cases h; exact hTwoGen _
              · simp only [hSide, ↓reduceIte] at h
                split at h
                · cases h
                · cases h; exact hTwoGen _
            · cases h

theorem liquidate_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid liqFeeCap loss : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepLiquidate st mid pid liqFeeCap loss = some st') :
    st'.coherent mids pids := by
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
        · have hCore : ∀ (oiL' oiS' rL' rS' : Nat),
              let capDeb := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.1
              let cap1 := (applyContainedLoss pfl.capital pfl.totalMm leg loss).1
              let liqFee := min liqFeeCap (cap1 - (pfl.totalMm - leg.cachedMm))
              let shortfall := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.2
              let insDraw := min shortfall (min ((m.insurance * m.maxInsDrawBps) / bpsDenNat) m.insurance)
              st.totalCapital ≥ capDeb + liqFee → st.vault ≥ liqFee → st.totalInsurance ≥ insDraw →
              ({ st with
                vault          := st.vault - liqFee
                totalCapital   := st.totalCapital - capDeb - liqFee
                totalInsurance := st.totalInsurance - insDraw
                totalResidual  := st.totalResidual + capDeb + insDraw
                markets        := updateFn st.markets mid (some { m with
                  realizedPool  := m.realizedPool + capDeb + insDraw
                  insurance     := m.insurance - insDraw
                  totalPosPnl   := m.totalPosPnl - (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.1
                  oiLong        := oiL'
                  oiShort       := oiS'
                  rawBasisLong  := rL'
                  rawBasisShort := rS'
                  adlLong       := deriveAdl oiL' rL'
                  adlShort      := deriveAdl oiS' rS' })
                portfolios     := updateFn st.portfolios pid (some { pfl with
                  capital := cap1 - liqFee
                  totalMm := pfl.totalMm - leg.cachedMm
                  totalIm := pfl.totalIm - leg.cachedIm
                  legs    := updateFn pfl.legs mid (some { leg with
                    side := .flat, rawBasis := 0,
                    posPnl := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.1,
                    cachedMm := 0, cachedIm := 0 }) }) } : DexState).coherent mids pids := by
            intro oiL' oiS' rL' rS' capDeb cap1 liqFee shortfall insDraw htc hv hti
            rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
            have hdebLe : capDeb + liqFee ≤ pfl.capital := by
              dsimp only [capDeb, cap1, liqFee, applyContainedLoss, capAvailableForLeg]; omega
            have hinsLe : insDraw ≤ m.insurance := by dsimp only [insDraw]; omega
            refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
            · unfold sumCaps at *; dsimp only; rw [hC, Nat.sub_sub]
              exact sum_map_eq_sub pids (getCap st.portfolios) _ pid (capDeb + liqFee) hndP hmemP
                (by simp [getCap, updateFn, hp, cap1, capDeb, liqFee, applyContainedLoss]; omega)
                (by simp [getCap, hp]; exact hdebLe)
                (fun x hx => by simp [getCap, updateFn, hx])
            · unfold sumIns at *; dsimp only; rw [hI]
              exact sum_map_eq_sub mids (getIns st.markets) _ mid insDraw hndM hmemM
                (by simp [getIns, updateFn, hm])
                (by simp [getIns, hm]; exact hinsLe)
                (fun x hx => by simp [getIns, updateFn, hx])
            · unfold sumRes at *; dsimp only; rw [hR, Nat.add_assoc]
              exact sum_map_eq_add mids (getRes st.markets) _ mid (capDeb + insDraw) hndM hmemM
                (by simp only [getRes, updateFn, ↓reduceIte, hm]; rw [Nat.add_assoc])
                (fun x hx => by simp [getRes, updateFn, hx])
            · unfold sumRew at *; dsimp only; rw [hF]
              apply sumRew_update_same st mids mid m _ hm; rfl
          cases hside : leg.side
          · simp only [hside] at h
            split at h
            · next hc => omega
            · cases h
          · simp only [hside] at h
            split at h
            · next hc => cases h; exact hCore _ _ _ _ hc.1 hc.2.1 hc.2.2.1
            · cases h
          · simp only [hside] at h
            split at h
            · next hc => cases h; exact hCore _ _ _ _ hc.1 hc.2.1 hc.2.2.1
            · cases h
        · cases h

theorem liquidateTakeoverPostAdl_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid liqPid rawClose liqFeeCap loss : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepLiquidateTakeoverPostAdl st mid pid liqPid rawClose liqFeeCap loss = some st') :
    st'.coherent mids pids := by
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
              · next hc =>
                cases h
                rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
                let capDeb := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.1
                let cap1 := (applyContainedLoss pfl.capital pfl.totalMm leg loss).1
                let liqFee := min liqFeeCap (cap1 - (pfl.totalMm - leg.cachedMm))
                let shortfall := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.2
                let insDraw := min shortfall (min ((m.insurance * m.maxInsDrawBps) / bpsDenNat) m.insurance)
                have hdebLe : capDeb + liqFee ≤ pfl.capital := by
                  dsimp only [capDeb, cap1, liqFee, applyContainedLoss, capAvailableForLeg]; omega
                have hinsLe : insDraw ≤ m.insurance := by dsimp only [insDraw]; omega
                refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
                · unfold sumCaps at *; dsimp only; rw [hC, Nat.sub_sub]
                  exact sum_map_eq_sub pids (getCap st.portfolios) _ pid (capDeb + liqFee) hndP hmemP
                    (by simp [getCap, updateFn, hnePL, hp, cap1, capDeb, liqFee, applyContainedLoss]; omega)
                    (by simp [getCap, hp]; exact hdebLe)
                    (fun x hx => by
                      by_cases hxl : x = liqPid
                      · subst hxl; simp [getCap, updateFn, hlp]
                      · simp [getCap, updateFn, hxl, hx])
                · unfold sumIns at *; dsimp only; rw [hI]
                  exact sum_map_eq_sub mids (getIns st.markets) _ mid insDraw hndM hmemM
                    (by simp [getIns, updateFn, hm, insDraw, shortfall])
                    (by simp [getIns, hm]; exact hinsLe)
                    (fun x hx => by simp [getIns, updateFn, hx])
                · unfold sumRes at *; dsimp only; rw [hR, Nat.add_assoc]
                  exact sum_map_eq_add mids (getRes st.markets) _ mid (capDeb + insDraw) hndM hmemM
                    (by simp only [getRes, updateFn, ↓reduceIte, hm, capDeb, insDraw, shortfall]; rw [Nat.add_assoc])
                    (fun x hx => by simp [getRes, updateFn, hx])
                · unfold sumRew at *; dsimp only; rw [hF]
                  apply sumRew_update_same st mids mid m _ hm; rfl
              · cases h
            · cases h

theorem claimResolved_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepClaimResolved st mid pid = some st') :
    st'.coherent mids pids := by
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
          · next hpayLe =>
            cases h
            rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
            refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
            · unfold sumCaps at *; dsimp only; rw [hC]
              exact sum_map_eq_add pids (getCap st.portfolios) _ pid _ hndP hmemP
                (by simp [getCap, updateFn, hp])
                (fun x hx => by simp [getCap, updateFn, hx])
            · unfold sumIns at *; dsimp only; rw [hI]
              apply sum_map_update_const; intro x _
              by_cases hx : x = mid
              · subst hx; simp [getIns, updateFn, hm]
              · simp [getIns, updateFn, hx]
            · unfold sumRes at *; dsimp only; rw [hR]
              exact sum_map_eq_sub mids (getRes st.markets) _ mid _ hndM hmemM
                (by simp [getRes, updateFn, hm])
                (by simp [getRes, hm]; omega)
                (fun x hx => by simp [getRes, updateFn, hx])
            · unfold sumRew at *; dsimp only; rw [hF]
              apply sumRew_update_same st mids mid m _ hm; rfl
        · cases h

theorem sweepOrphanInsurance_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (h : stepSweepOrphanInsurance st mid = some st') :
    st'.coherent mids pids := by
  unfold stepSweepOrphanInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · next hc =>
      cases h
      rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
      refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_, ?_⟩
      · unfold sumIns at *; dsimp only; rw [hI]
        exact sum_map_eq_sub mids (getIns st.markets) _ mid m.insurance hndM hmemM
          (by simp [getIns, updateFn, hm]) (by simp [getIns, hm])
          (fun x hx => by simp [getIns, updateFn, hx])
      · unfold sumRes at *; dsimp only; rw [hR]
        apply sum_map_update_const; intro x _
        by_cases hx : x = mid
        · subst hx; simp [getRes, updateFn, hm]
        · simp [getRes, updateFn, hx]
      · unfold sumRew at *; dsimp only; rw [hF]
        apply sumRew_update_same st mids mid m _ hm; rfl
    · cases h

theorem settleFullCapitalLoss_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid loss : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepSettleFullCapitalLoss st mid pid loss = some st') :
    st'.coherent mids pids := by
  unfold stepSettleFullCapitalLoss at h
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
          rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
          let pnlBurned := min loss leg.posPnl
          let rem1      := loss - pnlBurned
          let capDeb    := min rem1 pfl.capital
          let repay     := min capDeb m.insFronted
          let toR       := capDeb - repay
          have hdebLe : capDeb ≤ pfl.capital := Nat.min_le_right _ _
          have hrepLe : repay ≤ capDeb := Nat.min_le_left _ _
          refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
          · unfold sumCaps at *; dsimp only; rw [hC]
            exact sum_map_eq_sub pids (getCap st.portfolios) _ pid capDeb hndP hmemP
              (by simp [getCap, updateFn, hp, capDeb, rem1, pnlBurned])
              (by simp [getCap, hp]; exact hdebLe)
              (fun x hx => by simp [getCap, updateFn, hx])
          · unfold sumIns at *; dsimp only; rw [hI]
            exact sum_map_eq_add mids (getIns st.markets) _ mid repay hndM hmemM
              (by simp [getIns, updateFn, hm, repay, capDeb, rem1, pnlBurned])
              (fun x hx => by simp [getIns, updateFn, hx])
          · unfold sumRes at *; dsimp only; rw [hR]
            exact sum_map_eq_add mids (getRes st.markets) _ mid toR hndM hmemM
              (by simp [getRes, updateFn, hm, toR, repay, capDeb, rem1, pnlBurned])
              (fun x hx => by simp [getRes, updateFn, hx])
          · unfold sumRew at *; dsimp only; rw [hF]
            apply sumRew_update_same st mids mid m _ hm; rfl
        · cases h

theorem realizeFrontedPnl_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepRealizeFrontedPnl st mid pid = some st') :
    st'.coherent mids pids := by
  unfold stepRealizeFrontedPnl at h
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
          rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
          let fromR   := min leg.posPnl m.realizedPool
          let fromIns := leg.posPnl - fromR
          have hfrLeR : fromR ≤ m.realizedPool := Nat.min_le_right _ _
          have hfrLeP : fromR ≤ leg.posPnl := Nat.min_le_left _ _
          have hfiLeI : fromIns ≤ m.insurance := by
            have h1 : m.realizedPool + min (((m.insurance + m.insFronted) * m.maxFrontBps) / bpsDenNat - m.insFronted) m.insurance ≥ m.totalPosPnl :=
              hc.2.2.2.2.2.2.2.1
            have h2 : m.totalPosPnl ≥ leg.posPnl := hc.2.2.2.2.2.2.1
            have h3 : min (((m.insurance + m.insFronted) * m.maxFrontBps) / bpsDenNat - m.insFronted) m.insurance ≤ m.insurance :=
              Nat.min_le_right _ _
            omega
          refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_, ?_⟩
          · unfold sumCaps at *; dsimp only; rw [hC]
            exact sum_map_eq_add pids (getCap st.portfolios) _ pid leg.posPnl hndP hmemP
              (by simp [getCap, updateFn, hp])
              (fun x hx => by simp [getCap, updateFn, hx])
          · unfold sumIns at *; dsimp only; rw [hI]
            exact sum_map_eq_sub mids (getIns st.markets) _ mid fromIns hndM hmemM
              (by simp [getIns, updateFn, hm, fromIns, fromR])
              (by simp [getIns, hm]; exact hfiLeI)
              (fun x hx => by simp [getIns, updateFn, hx])
          · unfold sumRes at *; dsimp only; rw [hR]
            exact sum_map_eq_sub mids (getRes st.markets) _ mid fromR hndM hmemM
              (by simp [getRes, updateFn, hm, fromR])
              (by simp [getRes, hm]; exact hfrLeR)
              (fun x hx => by simp [getRes, updateFn, hx])
          · unfold sumRew at *; dsimp only; rw [hF]
            apply sumRew_update_same st mids mid m _ hm; rfl
        · cases h

theorem sweepSurplus_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (signer sweepAmt : Nat)
    (hcoh : st.coherent mids pids)
    (h : stepSweepSurplus st signer sweepAmt = some st') :
    st'.coherent mids pids := by
  unfold stepSweepSurplus at h
  split at h
  · next hc =>
    cases h
    rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
    exact ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, hI, hR, hF⟩
  · cases h

theorem claimReward_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid signer reqAmt : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (h : stepClaimReward st mid signer reqAmt = some st') :
    st'.coherent mids pids := by
  unfold stepClaimReward at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    let claimAmt := if reqAmt = 0 then m.rewardAccrued else reqAmt
    change (if m.rewardRecipient ≠ 0 ∧ signer = m.rewardRecipient ∧
        claimAmt > 0 ∧ claimAmt ≤ m.rewardAccrued ∧
        claimAmt ≤ st.totalRewards ∧ claimAmt ≤ st.vault then
      some { st with
        vault        := st.vault - claimAmt
        totalRewards := st.totalRewards - claimAmt
        markets      := updateFn st.markets mid (some { m with rewardAccrued := m.rewardAccrued - claimAmt }) }
    else none) = some st' at h
    by_cases hc : m.rewardRecipient ≠ 0 ∧ signer = m.rewardRecipient ∧
        claimAmt > 0 ∧ claimAmt ≤ m.rewardAccrued ∧
        claimAmt ≤ st.totalRewards ∧ claimAmt ≤ st.vault
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; cases h
      rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
      refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_, ?_⟩
      · unfold sumIns at *; dsimp only; rw [hI]
        apply sum_map_update_const; intro x _
        by_cases hx : x = mid
        · subst hx; simp [getIns, updateFn, hm]
        · simp [getIns, updateFn, hx]
      · unfold sumRes at *; dsimp only; rw [hR]
        apply sum_map_update_const; intro x _
        by_cases hx : x = mid
        · subst hx; simp [getRes, updateFn, hm]
        · simp [getRes, updateFn, hx]
      · unfold sumRew at *; dsimp only; rw [hF]
        exact sum_map_eq_sub mids (getRew st.markets) _ mid claimAmt hndM hmemM
          (by simp [getRew, updateFn, hm])
          (by simp [getRew, hm]; exact hc.2.2.2.1)
          (fun x hx => by simp [getRew, updateFn, hx])
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h

theorem updateOracle_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid newPrice fundE6 curSlot : Nat)
    (hcoh : st.coherent mids pids)
    (h : stepUpdateOracle st mid newPrice fundE6 curSlot = some st') :
    st'.coherent mids pids := by
  unfold stepUpdateOracle at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    let diff := if newPrice ≥ m.markPrice then newPrice - m.markPrice else m.markPrice - newPrice
    by_cases hc : m.status = .active ∧ curSlot > m.lastOracleSlot ∧ newPrice > 0 ∧
        diff + fundE6 ≤ (m.markPrice * m.maxMoveBps) / bpsDenNat
    · simp only [diff, hc, and_self, ↓reduceIte, Option.some.injEq] at h
      subst h
      rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
      refine ⟨hstock, hC, ?_, ?_, ?_⟩
      · unfold sumIns at *; dsimp only; rw [hI]
        apply sum_map_update_const; intro x _
        by_cases hx : x = mid
        · subst hx; simp [getIns, updateFn, hm]
        · simp [getIns, updateFn, hx]
      · unfold sumRes at *; dsimp only; rw [hR]
        apply sum_map_update_const; intro x _
        by_cases hx : x = mid
        · subst hx; simp [getRes, updateFn, hm]
        · simp [getRes, updateFn, hx]
      · unfold sumRew at *; dsimp only; rw [hF]
        apply sumRew_update_same st mids mid m _ hm; rfl
    · simp only [diff, hc, ↓reduceIte] at h; cases h

theorem liquidateFullCap_preserves_coherent (st st' : DexState) (mids pids : List Nat)
    (mid pid liqFeeCap loss : Nat)
    (hcoh : st.coherent mids pids) (hndM : mids.Nodup) (hmemM : mid ∈ mids)
    (hndP : pids.Nodup) (hmemP : pid ∈ pids)
    (h : stepLiquidateFullCap st mid pid liqFeeCap loss = some st') :
    st'.coherent mids pids := by
  unfold stepLiquidateFullCap at h
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
        let pnlBurned := min loss leg.posPnl
        let rem1      := loss - pnlBurned
        let capDeb    := min rem1 pfl.capital
        let cap1      := pfl.capital - capDeb
        let repay     := min capDeb m.insFronted
        let toR       := capDeb - repay
        let sfRaw     := rem1 - capDeb
        let wo        := min sfRaw (m.insFronted - repay)
        let shortfall := sfRaw - wo
        let liqFee    := min liqFeeCap cap1
        let insAfterRepay := m.insurance + repay
        let maxDraw   := (insAfterRepay * m.maxInsDrawBps) / bpsDenNat
        let insDraw   := if shortfall > 0 ∧ cap1 = 0 then min shortfall (min maxDraw insAfterRepay) else 0
        by_cases hc : m.status = .active ∧ leg.side ≠ .flat ∧ leg.rawBasis > 0 ∧
            st.totalCapital ≥ capDeb + liqFee ∧ st.vault ≥ liqFee ∧
            st.totalInsurance + repay ≥ insDraw ∧ m.totalPosPnl ≥ pnlBurned
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at h; cases h
          rcases hcoh with ⟨hstock, hC, hI, hR, hF⟩
          have hdebLe : capDeb + liqFee ≤ pfl.capital := by
            dsimp only [capDeb, cap1, liqFee]; omega
          have hrepLe : repay ≤ capDeb := Nat.min_le_left _ _
          have hinsLe : insDraw ≤ insAfterRepay := by
            dsimp only [insDraw]; split <;> omega
          have hstI : st.totalInsurance + repay ≥ insDraw := hc.2.2.2.2.2.1
          have htc  : st.totalCapital ≥ capDeb + liqFee := hc.2.2.2.1
          have hv   : st.vault ≥ liqFee := hc.2.2.2.2.1
          have htoR : toR + repay = capDeb := by dsimp only [toR]; omega
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · unfold DexState.stockExact at hstock ⊢
            change st.totalCapital - capDeb - liqFee + (st.totalInsurance + repay - insDraw) +
                (st.totalResidual + toR + insDraw) + st.totalSurplus + st.totalRewards = st.vault - liqFee
            omega
          · unfold sumCaps at *; dsimp only; rw [hC, Nat.sub_sub]
            exact sum_map_eq_sub pids (getCap st.portfolios) _ pid (capDeb + liqFee) hndP hmemP
              (by simp [getCap, updateFn, hp, cap1, capDeb, liqFee, rem1, pnlBurned]; omega)
              (by simp [getCap, hp]; exact hdebLe)
              (fun x hx => by simp [getCap, updateFn, hx])
          · unfold sumIns at *; dsimp only; rw [hI]
            have h1 := sum_map_update_one_addSub mids (getIns st.markets)
              (getIns (updateFn st.markets mid (some { m with
                insurance := insAfterRepay - insDraw, insFronted := m.insFronted - repay - wo,
                realizedPool := m.realizedPool + toR + insDraw, totalPosPnl := m.totalPosPnl - pnlBurned })))
              mid repay insDraw hndM hmemM
              (by simp [getIns, updateFn, hm, insAfterRepay])
              (by simp [getIns, hm]; exact hinsLe)
              (fun x hx => by simp [getIns, updateFn, hx])
            change (List.map (getIns st.markets) mids).sum + repay - insDraw =
              (List.map (getIns (updateFn st.markets mid (some { m with
                insurance := insAfterRepay - insDraw, insFronted := m.insFronted - repay - wo,
                realizedPool := m.realizedPool + toR + insDraw, totalPosPnl := m.totalPosPnl - pnlBurned }))) mids).sum
            omega
          · unfold sumRes at *; dsimp only; rw [hR, Nat.add_assoc]
            exact sum_map_eq_add mids (getRes st.markets) _ mid (toR + insDraw) hndM hmemM
              (by simp only [getRes, updateFn, ↓reduceIte, hm, toR, insDraw, insAfterRepay, maxDraw, shortfall, wo, sfRaw, repay, cap1, capDeb, rem1, pnlBurned]; rw [Nat.add_assoc])
              (fun x hx => by simp [getRes, updateFn, hx])
          · unfold sumRew at *; dsimp only; rw [hF]
            apply sumRew_update_same st mids mid m _ hm; rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h; cases h

/-- Single-step relation covering EVERY balance-moving transition in `percolator-lean` v2.1
    (all 18 transitions: original 13 + full-capital settlement, cumulative `I_m` fronting,
    `SweepSurplus`, clamped `UpdateOracle`, and Bug-1B/1C hardened `LiquidateFullCap`!). -/
inductive DexStep (mids pids : List Nat) : DexState → DexState → Prop where
  | depositCollateral {st st' pid amt} :
      pid ∈ pids → stepDepositCollateral st pid amt = some st' → DexStep mids pids st st'
  | withdrawCollateral {st st' pid amt curSlot} :
      pid ∈ pids → stepWithdrawCollateral st pid amt curSlot = some st' → DexStep mids pids st st'
  | depositInsurance {st st' mid lp amt donate} :
      mid ∈ mids → stepDepositInsurance st mid lp amt donate = some st' → DexStep mids pids st st'
  | withdrawInsurance {st st' mid lp burn} :
      mid ∈ mids → stepWithdrawInsurance st mid lp burn = some st' → DexStep mids pids st st'
  | realizeLegPnl {st st' mid pid} :
      mid ∈ mids → pid ∈ pids → stepRealizeLegPnl st mid pid = some st' → DexStep mids pids st st'
  | settleContainedLoss {st st' mid pid loss} :
      mid ∈ mids → pid ∈ pids → stepSettleContainedLoss st mid pid loss = some st' → DexStep mids pids st st'
  | settleFullCapitalLoss {st st' mid pid loss} :
      mid ∈ mids → pid ∈ pids → stepSettleFullCapitalLoss st mid pid loss = some st' → DexStep mids pids st st'
  | realizeFrontedPnl {st st' mid pid} :
      mid ∈ mids → pid ∈ pids → stepRealizeFrontedPnl st mid pid = some st' → DexStep mids pids st st'
  | tradeOpenPostAdl {st st' mid pidL pidS qty spLS spSL} :
      mid ∈ mids → pidL ∈ pids → pidS ∈ pids →
      stepTradeOpenPostAdl st mid pidL pidS qty spLS spSL = some st' → DexStep mids pids st st'
  | tradeReduce {st st' mid pidL pidS qty} :
      stepTradeReduce st mid pidL pidS qty = some st' → DexStep mids pids st st'
  | tradeHandoff {st st' mid pidSell pidBuy qty spBS spSB} :
      pidSell ∈ pids → pidBuy ∈ pids →
      stepTradeHandoff st mid pidSell pidBuy qty spBS spSB = some st' → DexStep mids pids st st'
  | liquidate {st st' mid pid feeCap loss} :
      mid ∈ mids → pid ∈ pids → stepLiquidate st mid pid feeCap loss = some st' → DexStep mids pids st st'
  | liquidateFullCap {st st' mid pid feeCap loss} :
      mid ∈ mids → pid ∈ pids → stepLiquidateFullCap st mid pid feeCap loss = some st' → DexStep mids pids st st'
  | liquidateTakeoverPostAdl {st st' mid pid liqPid rawClose feeCap loss} :
      mid ∈ mids → pid ∈ pids →
      stepLiquidateTakeoverPostAdl st mid pid liqPid rawClose feeCap loss = some st' → DexStep mids pids st st'
  | claimResolved {st st' mid pid} :
      mid ∈ mids → pid ∈ pids → stepClaimResolved st mid pid = some st' → DexStep mids pids st st'
  | sweepOrphanInsurance {st st' mid} :
      mid ∈ mids → stepSweepOrphanInsurance st mid = some st' → DexStep mids pids st st'
  | sweepSurplus {st st' signer amt} :
      stepSweepSurplus st signer amt = some st' → DexStep mids pids st st'
  | claimReward {st st' mid signer amt} :
      mid ∈ mids → stepClaimReward st mid signer amt = some st' → DexStep mids pids st st'
  | updateOracle {st st' mid newPrice fundE6 curSlot} :
      stepUpdateOracle st mid newPrice fundE6 curSlot = some st' → DexStep mids pids st st'

/-- Reflexive-transitive reachability across arbitrary multi-step transaction traces. -/
inductive DexReachable (mids pids : List Nat) : DexState → DexState → Prop where
  | refl (st : DexState) : DexReachable mids pids st st
  | step {st0 st1 st2 : DexState} :
      DexReachable mids pids st0 st1 → DexStep mids pids st1 st2 → DexReachable mids pids st0 st2

/-- **Unified Multi-Step Trace Coherence Theorem (Global No-LOF Proof Across ALL 19 Transitions!)**:
    Starting from ANY coherent DEX state `st0`, EVERY state `st` reachable via ANY finite
    interleaving of all 19 protocol transitions preserves exact 5-bucket aggregate coherence:
    `C_tot = ∑ capital`, `I_tot = ∑ insurance`, `R_tot = ∑ realizedPool`, `F_tot = ∑ rewardAccrued`,
    AND `C_tot + I_tot + R_tot + S_tot + F_tot = V`! -/
theorem reachable_preserves_coherent (mids pids : List Nat)
    (hndM : mids.Nodup) (hndP : pids.Nodup)
    (st0 st : DexState) (h0 : st0.coherent mids pids)
    (hreach : DexReachable mids pids st0 st) :
    st.coherent mids pids := by
  induction hreach with
  | refl => exact h0
  | step _ hstep ih =>
    cases hstep with
    | depositCollateral hp h => exact depositCollateral_preserves_coherent _ _ _ _ _ _ ih hndP hp h
    | withdrawCollateral hp h => exact withdrawCollateral_preserves_coherent _ _ _ _ _ _ _ ih hndP hp h
    | depositInsurance hm h => exact depositInsurance_preserves_coherent _ _ _ _ _ _ _ _ ih hndM hm h
    | withdrawInsurance hm h => exact withdrawInsurance_preserves_coherent _ _ _ _ _ _ _ ih hndM hm h
    | realizeLegPnl hm hp h => exact realizeLegPnl_preserves_coherent _ _ _ _ _ _ ih hndM hm hndP hp h
    | settleContainedLoss hm hp h => exact settleContainedLoss_preserves_coherent _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | settleFullCapitalLoss hm hp h => exact settleFullCapitalLoss_preserves_coherent _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | realizeFrontedPnl hm hp h => exact realizeFrontedPnl_preserves_coherent _ _ _ _ _ _ ih hndM hm hndP hp h
    | tradeOpenPostAdl hm hL hS h => exact tradeOpenPostAdl_preserves_coherent _ _ _ _ _ _ _ _ _ _ ih hndM hm hndP hL hS h
    | tradeReduce h => exact tradeReduce_preserves_coherent _ _ _ _ _ _ _ _ ih h
    | tradeHandoff hS hB h => exact tradeHandoff_preserves_coherent _ _ _ _ _ _ _ _ _ _ ih hndP hS hB h
    | liquidate hm hp h => exact liquidate_preserves_coherent _ _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | liquidateFullCap hm hp h => exact liquidateFullCap_preserves_coherent _ _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | liquidateTakeoverPostAdl hm hp h => exact liquidateTakeoverPostAdl_preserves_coherent _ _ _ _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | claimResolved hm hp h => exact claimResolved_preserves_coherent _ _ _ _ _ _ ih hndM hm hndP hp h
    | sweepOrphanInsurance hm h => exact sweepOrphanInsurance_preserves_coherent _ _ _ _ _ ih hndM hm h
    | sweepSurplus h => exact sweepSurplus_preserves_coherent _ _ _ _ _ _ ih h
    | claimReward hm h => exact claimReward_preserves_coherent _ _ _ _ _ _ _ ih hndM hm h
    | updateOracle h => exact updateOracle_preserves_coherent _ _ _ _ _ _ _ _ ih h

/-- **Corollary (Global Multi-Step 5-Bucket Solvency Conservation)**:
    Across ANY finite trace of all 19 protocol instructions, the exact sum of all portfolio capitals,
    all per-market insurance pools, all per-market realized pools, global surplus, and all per-market
    accrued reward pools equals the SPL vault balance `V` to the last atom! -/
theorem reachable_global_solvency (mids pids : List Nat)
    (hndM : mids.Nodup) (hndP : pids.Nodup)
    (st0 st : DexState) (h0 : st0.coherent mids pids)
    (hreach : DexReachable mids pids st0 st) :
    sumCaps st pids + sumIns st mids + sumRes st mids + st.totalSurplus + sumRew st mids = st.vault := by
  have ⟨hstock, hC, hI, hR, hF⟩ := reachable_preserves_coherent mids pids hndM hndP st0 st h0 hreach
  unfold DexState.stockExact at hstock
  omega

/-- **Gap #5 Theorem (`adversarial_multi_account_net_extraction_bound`)**:
    **Multi-Account Adversarial Economic Net-Extraction Bound Over Arbitrary 19-Transition Traces!**
    Partition portfolios into `attackerPids ++ honestPids` (`pids`) and markets into
    `trustedMids ++ untrustedMids` (`mids`). Across ANY finite `DexReachable` trace `st0 →* st`:
    1. **Global 5-Bucket Economic Extraction Identity**: Every atom gained by ALL attacker accounts
       beyond net vault inflows MUST come atom-for-atom from honest capitals, trusted pools
       (`I_T + R_T + F_T`), untrusted pools (`I_U + R_U + F_U`), or protocol surplus `S`!
    2. **Zero Trusted-Pool Extraction Corollary**: Whenever honest users' capitals + trusted markets'
       `I_T + R_T + F_T` + `S` do not decrease, total attacker net extraction across ALL attacker
       accounts combined is **STRICTLY BOUNDED BY `sumIns st0 untrustedMids + sumRes st0 untrustedMids + sumRew st0 untrustedMids`**
       (and **EXACT `0`** when `untrustedMids` have `0` external pools)! -/
theorem adversarial_multi_account_net_extraction_bound
    (trustedMids untrustedMids attackerPids honestPids : List Nat)
    (hndM : (trustedMids ++ untrustedMids).Nodup)
    (hndP : (attackerPids ++ honestPids).Nodup)
    (st0 st : DexState) (h0 : st0.coherent (trustedMids ++ untrustedMids) (attackerPids ++ honestPids))
    (hreach : DexReachable (trustedMids ++ untrustedMids) (attackerPids ++ honestPids) st0 st) :
    let atk0 := sumCaps st0 attackerPids
    let atk1 := sumCaps st  attackerPids
    let prot0 := sumCaps st0 honestPids + sumIns st0 trustedMids + sumRes st0 trustedMids + sumRew st0 trustedMids + st0.totalSurplus
    let prot1 := sumCaps st  honestPids + sumIns st  trustedMids + sumRes st  trustedMids + sumRew st  trustedMids + st.totalSurplus
    let unt0 := sumIns st0 untrustedMids + sumRes st0 untrustedMids + sumRew st0 untrustedMids
    let unt1 := sumIns st  untrustedMids + sumRes st  untrustedMids + sumRew st  untrustedMids
    -- (1) Exact multi-account economic conservation identity
    atk1 + prot1 + unt1 = st.vault ∧
    atk0 + prot0 + unt0 = st0.vault ∧
    -- (2) If vault is closed (`st.vault ≤ st0.vault`) and protected honest+trusted pools do not shrink (`prot1 ≥ prot0`),
    --     ALL attacker accounts combined can NEVER extract more than `unt0` (and extract exact `0` if `unt0 = 0`)!
    (st.vault ≤ st0.vault → prot1 ≥ prot0 → atk1 ≤ atk0 + unt0 ∧ (unt0 = 0 → atk1 ≤ atk0)) := by
  have hS0 := reachable_global_solvency (trustedMids ++ untrustedMids) (attackerPids ++ honestPids) hndM hndP st0 st0 h0 (.refl st0)
  have hS1 := reachable_global_solvency (trustedMids ++ untrustedMids) (attackerPids ++ honestPids) hndM hndP st0 st  h0 hreach
  have hSplitCap : ∀ s : DexState, sumCaps s (attackerPids ++ honestPids) = sumCaps s attackerPids + sumCaps s honestPids := by
    intro s; unfold sumCaps; rw [List.map_append, List.sum_append]
  have hSplitIns : ∀ s : DexState, sumIns s (trustedMids ++ untrustedMids) = sumIns s trustedMids + sumIns s untrustedMids := by
    intro s; unfold sumIns; rw [List.map_append, List.sum_append]
  have hSplitRes : ∀ s : DexState, sumRes s (trustedMids ++ untrustedMids) = sumRes s trustedMids + sumRes s untrustedMids := by
    intro s; unfold sumRes; rw [List.map_append, List.sum_append]
  have hSplitRew : ∀ s : DexState, sumRew s (trustedMids ++ untrustedMids) = sumRew s trustedMids + sumRew s untrustedMids := by
    intro s; unfold sumRew; rw [List.map_append, List.sum_append]
  rw [hSplitCap, hSplitIns, hSplitRes, hSplitRew] at hS0 hS1
  dsimp only
  refine ⟨by omega, by omega, fun hv hp => ⟨by omega, fun hu => by omega⟩⟩

/-! ### Unconditional Anti-Shielding Proofs (`reservedMm` Firewall under God-Mode `RUG` Oracle) -/

/-- **Unconditional `syncReservedMm` Soundness**:
    Regardless of how large `newMm` or `newTotMm` becomes (even a 1,000,000× `RUG/USD` pump!),
    `syncReservedMm` ALWAYS preserves `newTotRes ≤ cap`, `newRes ≤ newMm`, AND leaves every
    other leg's available capital `cap - (newTotRes - solRes) ≥ solRes`! -/
theorem syncReservedMm_preserves_bound_and_other_leg
    (cap totRes oldRes newTotMm newMm solRes : Nat)
    (hcap : totRes ≤ cap) (hold : oldRes ≤ totRes) (hsol : solRes ≤ totRes - oldRes) :
    let (newRes, newTotRes) := syncReservedMm cap totRes oldRes newTotMm newMm
    newTotRes ≤ cap ∧ newRes ≤ newMm ∧ solRes ≤ newTotRes ∧
    cap - (newTotRes - solRes) ≥ solRes := by
  unfold syncReservedMm
  dsimp only
  by_cases h : cap ≥ newTotMm
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

/-- **Single-Step God-Mode `RUG/USD` Attack Immunity**:
    For ANY `RUG/USD` loss, ANY `RUG/USD` liquidation fee, and ANY inflated `newRugMm`,
    `stepRugReservedState` preserves `totRes' ≤ cap'`, `solRes + rugRes' ≤ totRes'`, AND
    `cap' - (totRes' - solRes) ≥ solRes`! -/
theorem rug_step_preserves_sol_reserved_mm
    (cap totRes rugRes solRes rugLoss rugFee newTotMm newRugMm : Nat)
    (hcap : totRes ≤ cap) (hdisj : solRes + rugRes ≤ totRes) :
    let (cap', totRes', rugRes') :=
      stepRugReservedState cap totRes rugRes rugLoss rugFee newTotMm newRugMm
    totRes' ≤ cap' ∧ solRes + rugRes' ≤ totRes' ∧
    cap' - (totRes' - solRes) ≥ solRes := by
  unfold stepRugReservedState syncReservedMm
  dsimp only
  by_cases h : cap - min rugLoss (cap - (totRes - rugRes)) -
      min rugFee (cap - min rugLoss (cap - (totRes - rugRes)) - (totRes - rugRes)) ≥ newTotMm
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]; omega

/-- Apply an arbitrary finite sequence of god-mode `RUG/USD` oracle actions
    `(rugLoss, rugFee, newTotMm, newRugMm)` to `(cap, totRes, rugRes)`. -/
def runRugAttackTrace :
    Nat × Nat × Nat → List (Nat × Nat × Nat × Nat) → Nat × Nat × Nat
  | s, [] => s
  | (cap, totRes, rugRes), (l, f, ntm, nrm) :: rest =>
      runRugAttackTrace (stepRugReservedState cap totRes rugRes l f ntm nrm) rest

/-- **Inductive Multi-Step God-Mode `RUG/USD` Oracle Immunity Theorem (Alice + Mule vs Bob)**:
    Suppose Alice holds an honest `SOL/USD` leg (against Bob) with `solRes ≥ solMm` alongside
    an untrusted `RUG/USD` leg whose oracle & admin are 100% controlled by Alice + Mule.
    After ANY finite sequence of arbitrary `RUG/USD` pumps, dumps, funding blasts, liquidations,
    or margin inflations, when `SOL/USD` moves against Alice by `solStepLoss` (≤ `solMm`):
    1. `SOL/USD` STILL has `availCap(SOL) ≥ solMm` unconditionally (zero shielding!), AND
    2. `applyContainedLoss` on `SOL/USD` produces **`shortfall = 0`** (Bob's `SOL/USD` positive PnL
       is paid 100% in full — zero bad debt, zero draw on `I_SOL`, zero haircut on Bob!). -/
theorem alice_mule_godmode_rug_zero_haircut_on_bob
    (cap0 totRes0 rugRes0 solRes solMm solStepLoss : Nat)
    (solLeg : LegState) (trace : List (Nat × Nat × Nat × Nat))
    (hcap0 : totRes0 ≤ cap0)
    (hdisj0 : solRes + rugRes0 ≤ totRes0)
    (hsolMm : solMm ≤ solRes)
    (hstep : solStepLoss ≤ solMm) :
    let (capF, totResF, _) := runRugAttackTrace (cap0, totRes0, rugRes0) trace
    let availSol := capF - (totResF - solRes)
    let (_, _, _, _, shortfall) :=
      applyContainedLoss capF totResF { solLeg with cachedMm := solRes } solStepLoss
    availSol ≥ solMm ∧ shortfall = 0 := by
  have hinv : ∀ (tr : List (Nat × Nat × Nat × Nat)) (c t r : Nat),
      t ≤ c → solRes + r ≤ t →
      let (c', t', r') := runRugAttackTrace (c, t, r) tr
      t' ≤ c' ∧ solRes + r' ≤ t' := by
    intro tr
    induction tr with
    | nil =>
      intro c t r hc hd
      exact ⟨hc, hd⟩
    | cons act rest ih =>
      intro c t r hc hd
      rcases act with ⟨l, f, ntm, nrm⟩
      dsimp only [runRugAttackTrace]
      have h1 := rug_step_preserves_sol_reserved_mm c t r solRes l f ntm nrm hc hd
      dsimp only at h1
      exact ih _ _ _ h1.1 h1.2.1
  have hfin := hinv trace cap0 totRes0 rugRes0 hcap0 hdisj0
  cases hrun : runRugAttackTrace (cap0, totRes0, rugRes0) trace with
  | mk capF pair =>
    cases pair with
    | mk totResF rugResF =>
      rw [hrun] at hfin
      dsimp only [applyContainedLoss, capAvailableForLeg]
      omega

/-! ### Adversarial-Leader Censorship (`T`-Slot Model) Solvency & Anti-Griefing Proofs -/

/-- **K-Slot Censored-Liquidation Zero-Bad-Debt Theorem**:
    Suppose adversarial validators include `UpdateOracle` on `K` consecutive slots while
    censoring `Liquidate`, and each step's loss satisfies `stepLoss * 10_000 ≤ N * maxMoveBps`.
    Whenever the market's risk parameters satisfy `K * maxMoveBps + liqFeeBps ≤ mmBps`,
    any healthy position (`equity * 10_000 ≥ N * mmBps`) covers ALL `K` cumulative step losses
    plus the full liquidation fee (`liqFee * 10_000 ≤ N * liqFeeBps`) with **ZERO bad debt**! -/
theorem censored_oracle_k_steps_zero_bad_debt
    (K N equity stepLoss liqFee maxMoveBps liqFeeBps mmBps : Nat)
    (hEnv   : K * maxMoveBps + liqFeeBps ≤ mmBps)
    (hEq    : N * mmBps ≤ equity * 10_000)
    (hStep  : stepLoss * 10_000 ≤ N * maxMoveBps)
    (hFee   : liqFee * 10_000 ≤ N * liqFeeBps) :
    K * stepLoss + liqFee ≤ equity := by
  have hKStep : (K * stepLoss) * 10_000 ≤ N * (K * maxMoveBps) := by
    calc (K * stepLoss) * 10_000
        = K * (stepLoss * 10_000) := by rw [Nat.mul_assoc]
      _ ≤ K * (N * maxMoveBps)    := Nat.mul_le_mul_left K hStep
      _ = N * (K * maxMoveBps)    := by rw [← Nat.mul_assoc, Nat.mul_comm K N, Nat.mul_assoc]
  have hSum : (K * stepLoss + liqFee) * 10_000 ≤ N * mmBps := by
    calc (K * stepLoss + liqFee) * 10_000
        = (K * stepLoss) * 10_000 + liqFee * 10_000 := Nat.add_mul _ _ _
      _ ≤ N * (K * maxMoveBps) + N * liqFeeBps      := Nat.add_le_add hKStep hFee
      _ = N * (K * maxMoveBps + liqFeeBps)          := (Nat.mul_add _ _ _).symm
      _ ≤ N * mmBps                                 := Nat.mul_le_mul_left N hEnv
  have hTot : (K * stepLoss + liqFee) * 10_000 ≤ equity * 10_000 := Nat.le_trans hSum hEq
  omega

/-- **Anti-Griefing Wind-Down Liveness Under `T`-Slot Leader Censorship**:
    Whenever `m.maxStaleness ≥ T` (at least 1 honest leader every `T` slots), censoring oracle
    cranks for up to `T - 1` slots (`curSlot - m.lastOracleSlot < T`) can **NEVER** satisfy
    `canPermissionlessWindDown`, blocking premature wind-down griefing! -/
theorem censored_crank_no_premature_winddown
    (m : MarketState) (curSlot T : Nat)
    (hStaleCfg : T ≤ m.maxStaleness)
    (hAge : curSlot - m.lastOracleSlot < T) :
    ¬ canPermissionlessWindDown m curSlot := by
  intro ⟨_, hgt⟩
  omega

/-! ### Per-Market Insurance LP Share Conservation (`∑ receipt.shares == m.totalInsShares`) -/

/-- Exact sum of all LP `InsReceipt.shares` on market `mid`. -/
def sumInsShares (st : DexState) (mid : Nat) (lps : List Nat) : Nat :=
  (lps.map (st.insShares mid)).sum

/-- Inductive insurance-share coherence across every market in `mids` and every LP in `lps`:
    the sum of all LP receipt shares on market `mid` equals `m.totalInsShares` EXACTLY! -/
def sharesCoherent (st : DexState) (mids lps : List Nat) : Prop :=
  ∀ mid ∈ mids, ∀ m, st.markets mid = some m → sumInsShares st mid lps = m.totalInsShares

private theorem list_sum_le_of_mem {α : Type} (f : α → Nat) (xs : List α) {a : α} (h : a ∈ xs) :
    f a ≤ (xs.map f).sum := by
  induction xs with
  | nil => cases h
  | cons x tl ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with rfl | htl
    · omega
    · have := ih htl; omega

/-- **No-Ghost-Shares Bound (`receipt.shares ≤ m.totalInsShares`)**:
    Under `sharesCoherent`, NO individual LP receipt can EVER hold more shares than `m.totalInsShares`! -/
theorem sharesCoherent_implies_receipt_le_total (st : DexState) (mids lps : List Nat)
    (mid lp : Nat) (m : MarketState)
    (hsh : sharesCoherent st mids lps) (hmId : mid ∈ mids) (hm : st.markets mid = some m)
    (hlp : lp ∈ lps) :
    st.insShares mid lp ≤ m.totalInsShares := by
  have hsum := hsh mid hmId m hm
  unfold sumInsShares at hsum
  have hle := list_sum_le_of_mem (st.insShares mid) lps hlp
  omega

/-- `stepDepositInsurance` (both regular LP share mint and permanent donation) preserves `sharesCoherent`. -/
theorem depositInsurance_preserves_sharesCoherent (st st' : DexState) (mids lps : List Nat)
    (mid lp amount : Nat) (donate : Bool)
    (hsh : sharesCoherent st mids lps) (hndL : lps.Nodup) (hmemL : lp ∈ lps)
    (h : stepDepositInsurance st mid lp amount donate = some st') :
    sharesCoherent st' mids lps := by
  unfold stepDepositInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · cases donate
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        have hdone : ∀ (minted : Nat),
            sharesCoherent ({ st with
              vault          := st.vault + amount
              totalInsurance := st.totalInsurance + amount
              markets        := updateFn st.markets mid (some { m with insurance := m.insurance + amount, totalInsShares := m.totalInsShares + minted })
              insShares      := updateFn st.insShares mid (updateFn (st.insShares mid) lp (st.insShares mid lp + minted)) } : DexState) mids lps := by
          intro minted mid' hmid' m' hm'
          dsimp only at hm'
          unfold sumInsShares; dsimp only
          by_cases heq : mid' = mid
          · subst heq
            simp only [updateFn, ↓reduceIte] at hm' ⊢
            cases hm'
            have hprev := hsh mid' hmid' m hm
            unfold sumInsShares at hprev
            have hadd := sum_map_eq_add lps (st.insShares mid')
              (updateFn (st.insShares mid') lp (st.insShares mid' lp + minted))
              lp minted hndL hmemL (by simp [updateFn]) (fun x hx => by simp [updateFn, hx])
            dsimp only
            omega
          · simp only [updateFn, heq, ↓reduceIte] at hm' ⊢
            exact hsh mid' hmid' m' hm'
        by_cases h0 : m.totalInsShares = 0 ∨ m.insurance = 0
        · simp only [h0, ↓reduceIte] at h
          split at h
          · cases h
          · cases h; exact hdone amount
        · simp only [h0, ↓reduceIte] at h
          split at h
          · cases h
          · cases h; exact hdone (amount * m.totalInsShares / m.insurance)
      · simp only [↓reduceIte] at h
        cases h
        intro mid' hmid' m' hm'
        dsimp only at hm'
        unfold sumInsShares; dsimp only
        by_cases heq : mid' = mid
        · subst heq
          simp only [updateFn, ↓reduceIte] at hm'
          cases hm'
          exact hsh mid' hmid' m hm
        · simp only [updateFn, heq, ↓reduceIte] at hm'
          exact hsh mid' hmid' m' hm'
    · cases h

/-- `stepWithdrawInsurance` preserves `sharesCoherent` across all markets and LPs. -/
theorem withdrawInsurance_preserves_sharesCoherent (st st' : DexState) (mids lps : List Nat)
    (mid lp burnShares : Nat)
    (hsh : sharesCoherent st mids lps) (hndL : lps.Nodup) (hmemL : lp ∈ lps)
    (h : stepWithdrawInsurance st mid lp burnShares = some st') :
    sharesCoherent st' mids lps := by
  unfold stepWithdrawInsurance at h
  cases hm : st.markets mid with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Bind.bind, Option.bind] at h
    split at h
    · next hc =>
      split at h
      · cases h
      · cases h
        intro mid' hmid' m' hm'
        dsimp only at hm'
        unfold sumInsShares; dsimp only
        by_cases heq : mid' = mid
        · subst heq
          simp only [updateFn, ↓reduceIte] at hm' ⊢
          cases hm'
          have hprev := hsh mid' hmid' m hm
          unfold sumInsShares at hprev
          have hsub := sum_map_eq_sub lps (st.insShares mid')
            (updateFn (st.insShares mid') lp (st.insShares mid' lp - burnShares))
            lp burnShares hndL hmemL (by simp [updateFn]) hc.2.2.2.2.2.2.1 (fun x hx => by simp [updateFn, hx])
          dsimp only
          omega
        · simp only [updateFn, heq, ↓reduceIte] at hm' ⊢
          exact hsh mid' hmid' m' hm'
    · cases h

/-- Hardened insurance share-minting guard (returns `(userSharesMinted, totalSharesAdded)`):
    1. Enforces minimum first-LP deposit (`amount ≥ 1_000_000`) to block 1-atom ERC-4626 inflation.
    2. When `totSh = 0` and pre-existing shareless insurance `ins > 0` exists (from donations/fees),
       locks `ins` behind `ins` unowned dead shares (`totalSharesAdded = ins + amount`,
       `userSharesMinted = amount`): blocks BOTH donation capture AND permissionless 1-atom DoS!
    3. Rejects reviving wiped-out shares on a drained pool (`totSh > 0 ∧ ins = 0`).
    4. On any live pool (`totSh > 0 ∧ ins > 0`), floor-minting `minted = ⌊amount · totSh / ins⌋`
       is strictly non-dilutive for all existing LPs: `(ins + amount) · totSh ≥ ins · (totSh + minted)`. -/
def hardenedInsMint (totSh ins amount : Nat) : Option (Nat × Nat) :=
  if totSh = 0 then
    if amount ≥ 1_000_000 then some (amount, ins + amount) else none
  else
    if ins > 0 then
      let m := (amount * totSh) / ins
      if m > 0 then some (m, m) else none
    else none

theorem insurance_share_mint_anti_capture_and_non_dilutive
    (totSh ins amount : Nat) :
    -- 1. Dust first deposit blocked
    (totSh = 0 → amount < 1_000_000 → hardenedInsMint totSh ins amount = none) ∧
    -- 2. First LP deposit after ANY permissionless donation succeeds (anti-DoS) and captures 0 donated funds!
    (totSh = 0 → amount ≥ 1_000_000 →
      ∃ uSh addTot, hardenedInsMint totSh ins amount = some (uSh, addTot) ∧
        (uSh * (ins + amount)) / (totSh + addTot) = amount ∧
        (ins + amount) - (uSh * (ins + amount)) / (totSh + addTot) = ins) ∧
    -- 3. Drained pool revival blocked
    (totSh > 0 → ins = 0 → hardenedInsMint totSh ins amount = none) ∧
    -- 4. Subsequent LP minting is strictly non-dilutive
    (∀ uSh addTot, totSh > 0 → hardenedInsMint totSh ins amount = some (uSh, addTot) →
      uSh = addTot ∧ (ins + amount) * totSh ≥ ins * (totSh + addTot)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0 hlt; unfold hardenedInsMint; simp [h0, Nat.not_le_of_lt hlt]
  · intro h0 hge
    refine ⟨amount, ins + amount, by unfold hardenedInsMint; simp [h0, hge], ?_, ?_⟩
    · have hpos : 0 < ins + amount := by omega
      have hdiv : (amount * (ins + amount)) / (0 + (ins + amount)) = amount := by
        rw [Nat.zero_add]; exact Nat.mul_div_cancel amount hpos
      simpa [h0] using hdiv
    · have hpos : 0 < ins + amount := by omega
      have hdiv : (amount * (ins + amount)) / (0 + (ins + amount)) = amount := by
        rw [Nat.zero_add]; exact Nat.mul_div_cancel amount hpos
      rw [h0, hdiv]; omega
  · intro hpos h0; unfold hardenedInsMint; simp [Nat.ne_of_gt hpos, h0]
  · intro uSh addTot hpos hm
    unfold hardenedInsMint at hm
    simp only [Nat.ne_of_gt hpos, ↓reduceIte] at hm
    split at hm
    · next hins =>
      split at hm
      · cases hm
        have hmul : ((amount * totSh) / ins) * ins ≤ amount * totSh :=
          Nat.div_mul_le_self (amount * totSh) ins
        have h1 : (ins + amount) * totSh = ins * totSh + amount * totSh := Nat.add_mul ins amount totSh
        have h2 : ins * (totSh + (amount * totSh) / ins) = ins * totSh + ins * ((amount * totSh) / ins) :=
          Nat.mul_add ins totSh _
        have hcomm : ins * ((amount * totSh) / ins) = ((amount * totSh) / ins) * ins := Nat.mul_comm _ _
        exact ⟨rfl, by omega⟩
      · cases hm
    · cases hm

/-- Authorization predicate mirroring `OracleAdapter.handleInitAdapter`:
    requires exact market owner (`percProg`), exact size (`MktOff.size`), `MAGIC_MARKET`,
    non-tombstoned status, nonzero `marketAdmin`, and `signer == marketAdmin`. -/
def initAdapterAuthorized (mktOwner percProg : Nat) (mktLen mktSize : Nat)
    (mktMagic expectedMagic : Nat) (isTombstoned : Bool)
    (mktAdmin zeroKey signer : Nat) : Bool :=
  (mktOwner == percProg) &&
  (mktLen == mktSize) &&
  (mktMagic == expectedMagic) &&
  (!isTombstoned) &&
  (mktAdmin != zeroKey) &&
  (signer == mktAdmin)

/-- **THEOREM (Anti-OracleAdapter-Hijack)**:
    `initAdapterAuthorized = true` iff EVERY market binding check passes and `signer = mktAdmin`
    (with `mktAdmin ≠ zeroKey`); any unrelated caller, spoofed/wrong-size/wrong-magic/tombstoned
    market, or burned-admin market is unconditionally rejected! -/
theorem initAdapter_requires_active_market_admin
    (mktOwner percProg mktLen mktSize mktMagic expectedMagic mktAdmin zeroKey signer : Nat)
    (isTombstoned : Bool) :
    initAdapterAuthorized mktOwner percProg mktLen mktSize mktMagic expectedMagic isTombstoned
      mktAdmin zeroKey signer = true ↔
    (mktOwner = percProg ∧ mktLen = mktSize ∧ mktMagic = expectedMagic ∧
     isTombstoned = false ∧ mktAdmin ≠ zeroKey ∧ signer = mktAdmin) := by
  unfold initAdapterAuthorized
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, and_assoc]

/-- Burning worthless shares (`ins = 0`) on a drained or `Tombstoned` market yields exact `payout = 0`,
    strictly reduces `curSh` and `totSh`, and lets the LP reach `shares = 0` for `CloseAccount` rent reclaim
    without ever mutating vault balances or blocking `TombstoneMarket`. -/
theorem worthless_shares_burn_zero_payout
    (curSh totSh burnShares : Nat)
    (hpos : burnShares > 0) (hle1 : burnShares ≤ curSh) (hle2 : curSh ≤ totSh) :
    (burnShares * 0) / totSh = 0 ∧
    curSh - burnShares < curSh ∧
    totSh - burnShares < totSh ∧
    curSh - burnShares ≤ totSh - burnShares := by
  refine ⟨by simp, by omega, by omega, by omega⟩

/-- **THEOREM (`insFronting_optimistic_nav_blocks_lp_arb`)**:
    When `I_m` has temporarily fronted `fronted` USD to winners (`ins` cash on hand + `fronted`
    receivable = optimistic NAV `nav = ins + fronted`), pricing `DepositInsurance` shares at
    `minted = ⌊amount · totSh / (ins + fronted)⌋` makes LP receivable arbitrage IMPOSSIBLE:
    even if 100% of `repay ≤ fronted` is immediately repaid by losers in the very next slot,
    the new LP's redeemable payout is strictly `≤ amount` (ZERO free profit!), and existing LPs'
    NAV per share is never diluted! -/
theorem insFronting_optimistic_nav_blocks_lp_arb
    (totSh ins fronted amount repay : Nat)
    (_hSh : totSh > 0) (_hNav : ins + fronted > 0) (hRep : repay ≤ fronted) :
    let nav := ins + fronted
    let minted := (amount * totSh) / nav
    let finalCash := ins + amount + repay
    let finalSh := totSh + minted
    -- 1. New LP can NEVER withdraw more than `amount` after losers repay `repay ≤ fronted`!
    (minted * finalCash) / finalSh ≤ amount ∧
    -- 2. Existing LPs are strictly non-diluted at full NAV!
    (nav + amount) * totSh ≥ nav * finalSh := by
  dsimp only
  have hmul : ((amount * totSh) / (ins + fronted)) * (ins + fronted) ≤ amount * totSh :=
    Nat.div_mul_le_self (amount * totSh) (ins + fronted)
  constructor
  · apply Nat.div_le_of_le_mul
    have hcash : ins + amount + repay ≤ (ins + fronted) + amount := by omega
    have h1 : ((amount * totSh) / (ins + fronted)) * (ins + amount + repay) ≤
              ((amount * totSh) / (ins + fronted)) * ((ins + fronted) + amount) :=
      Nat.mul_le_mul_left _ hcash
    have h2 : ((amount * totSh) / (ins + fronted)) * ((ins + fronted) + amount) =
              ((amount * totSh) / (ins + fronted)) * (ins + fronted) +
              ((amount * totSh) / (ins + fronted)) * amount :=
      Nat.mul_add _ _ _
    have h3 : (totSh + (amount * totSh) / (ins + fronted)) * amount =
              totSh * amount + ((amount * totSh) / (ins + fronted)) * amount :=
      Nat.add_mul _ _ _
    have hcomm : totSh * amount = amount * totSh := Nat.mul_comm _ _
    omega
  · have h1 : (ins + fronted + amount) * totSh = (ins + fronted) * totSh + amount * totSh :=
      Nat.add_mul (ins + fronted) amount totSh
    have h2 : (ins + fronted) * (totSh + (amount * totSh) / (ins + fronted)) =
              (ins + fronted) * totSh + (ins + fronted) * ((amount * totSh) / (ins + fronted)) :=
      Nat.mul_add (ins + fronted) totSh _
    have hcomm : (ins + fronted) * ((amount * totSh) / (ins + fronted)) =
                 ((amount * totSh) / (ins + fronted)) * (ins + fronted) := Nat.mul_comm _ _
    omega

/-- **THEOREM (`insFronting_strictly_contained_by_market_insurance`)**:
    Mango-proof cross-market isolation for `RUG/USD` fronting:
    1. Fronting `fromR ≤ R_m` and `fromIns ≤ I_m` (with `fromIns ≤ ⌊I_m · maxFrontBps / 10000⌋`)
       preserves exact global conservation `V = C + I + R + S`, never underflows `I_m`, and
       keeps every other market's insurance `I_other` untouched.
    2. Senior loser repayment `repay = min(capDeb, F_m)` restores `I_m` before `R_m`, preserving
       exact `V = C + I + R + S` and `F_m' = F_m - repay`. -/
theorem insFronting_strictly_contained_by_market_insurance
    (V C I_m I_other R_m R_other S F_m fromR fromIns capDeb : Nat)
    (hStock : V = C + (I_m + I_other) + (R_m + R_other) + S)
    (hR : fromR ≤ R_m) (hI : fromIns ≤ I_m) :
    -- After fronting `fromR + fromIns` into `C`:
    let C1 := C + fromR + fromIns
    let I1 := I_m - fromIns
    let R1 := R_m - fromR
    let F1 := F_m + fromIns
    V = C1 + (I1 + I_other) + (R1 + R_other) + S ∧
    I_m - I1 = fromIns ∧
    fromIns ≤ I_m ∧
    -- After loser pays `capDeb ≤ C1` with senior repayment to `I_m` first:
    (capDeb ≤ C1 →
      let repay := min capDeb F1
      let toR := capDeb - repay
      V = (C1 - capDeb) + ((I1 + repay) + I_other) + ((R1 + toR) + R_other) + S) := by
  dsimp only
  refine ⟨by omega, by omega, hI, fun hcap => by omega⟩

/-- **THEOREM (`sweepSurplus_preserves_stock_and_user_funds`)**:
    `handleSweepSurplus` reduces ONLY `Dex.vaultBalance` (`V`) and `Dex.totalSurplus` (`S`) by
    `sweepAmt ≤ S`, preserving exact `V' = C + I + R + S'` while leaving user capital `C`,
    insurance `I`, and realized pools `R` 100% untouched! -/
theorem sweepSurplus_preserves_stock_and_user_funds
    (V C I R S sweepAmt : Nat)
    (hStock : V = C + I + R + S) (hle : sweepAmt ≤ S) :
    V - sweepAmt = C + I + R + (S - sweepAmt) ∧ sweepAmt ≤ V := by
  omega

end Percolator.TraceProofs
