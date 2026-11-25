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
          rcases hcoh with ⟨hstock, hC, hI, hR⟩
          refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_⟩
          · unfold sumIns at *; dsimp only; rw [hI]
            exact sum_map_eq_add mids (getIns st.markets) _ mid amount hndM hmemM
              (by simp [getIns, updateFn, hm]) (fun x hx => by simp [getIns, updateFn, hx])
          · unfold sumRes at *; dsimp only; rw [hR]
            apply sum_map_update_const; intro x _
            by_cases hx : x = mid
            · subst hx; simp [getRes, updateFn, hm]
            · simp [getRes, updateFn, hx]
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
        rcases hcoh with ⟨hstock, hC, hI, hR⟩
        refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_⟩
        · unfold sumIns at *; dsimp only; rw [hI]
          exact sum_map_eq_add mids (getIns st.markets) _ mid amount hndM hmemM
            (by simp [getIns, updateFn, hm]) (fun x hx => by simp [getIns, updateFn, hx])
        · unfold sumRes at *; dsimp only; rw [hR]
          apply sum_map_update_const; intro x _
          by_cases hx : x = mid
          · subst hx; simp [getRes, updateFn, hm]
          · simp [getRes, updateFn, hx]
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
        rcases hcoh with ⟨hstock, hC, hI, hR⟩
        refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_⟩
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
          rcases hcoh with ⟨hstock, hC, hI, hR⟩
          have hdebLe : (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.1 ≤ pfl.capital := by
            unfold applyContainedLoss capAvailableForLeg; dsimp only; omega
          refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_⟩
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
          by_cases hc : m.status = .active ∧ qty > 0 ∧
              (m.rawBasisLong = 0 ∨ m.oiLong > 0) ∧
              (m.rawBasisShort = 0 ∨ m.oiShort > 0) ∧
              m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
              pL.capital + spSL ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spLS ∧
              pS.capital + spLS ≥ marginReq (marginNotional qty m.markPrice) m.tradeFeeBps + spSL ∧
              st.totalCapital ≥ 2 * marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
          · simp only [hc, and_self, ↓reduceIte, Option.some.injEq] at h
            subst h
            let fee := marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
            rcases hcoh with ⟨hstock, hC, hI, hR⟩
            refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_⟩
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
              exact sum_map_eq_add mids (getIns st.markets) _ mid (2 * fee) hndM hmemM
                (by simp [getIns, updateFn, hm, fee])
                (fun x hx => by simp [getIns, updateFn, hx])
            · unfold sumRes at *; dsimp only; rw [hR]
              apply sum_map_update_const; intro x _
              by_cases hx : x = mid
              · subst hx; simp [getRes, updateFn, hm]
              · simp [getRes, updateFn, hx]
          · simp only [hc, ↓reduceIte] at h; cases h

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
                    rcases hcoh with ⟨hstock, hC, hI, hR⟩
                    refine ⟨hstock, ?_, ?_, ?_⟩
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
                rcases hcoh with ⟨hstock, hC, hI, hR⟩
                refine ⟨hstock, ?_, hI, hR⟩
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
            rcases hcoh with ⟨hstock, hC, hI, hR⟩
            have hdebLe : capDeb + liqFee ≤ pfl.capital := by
              dsimp only [capDeb, cap1, liqFee, applyContainedLoss, capAvailableForLeg]; omega
            have hinsLe : insDraw ≤ m.insurance := by dsimp only [insDraw]; omega
            refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_⟩
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
                rcases hcoh with ⟨hstock, hC, hI, hR⟩
                let capDeb := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.1
                let cap1 := (applyContainedLoss pfl.capital pfl.totalMm leg loss).1
                let liqFee := min liqFeeCap (cap1 - (pfl.totalMm - leg.cachedMm))
                let shortfall := (applyContainedLoss pfl.capital pfl.totalMm leg loss).2.2.2.2
                let insDraw := min shortfall (min ((m.insurance * m.maxInsDrawBps) / bpsDenNat) m.insurance)
                have hdebLe : capDeb + liqFee ≤ pfl.capital := by
                  dsimp only [capDeb, cap1, liqFee, applyContainedLoss, capAvailableForLeg]; omega
                have hinsLe : insDraw ≤ m.insurance := by dsimp only [insDraw]; omega
                refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_⟩
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
            rcases hcoh with ⟨hstock, hC, hI, hR⟩
            refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, ?_, ?_, ?_⟩
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
      rcases hcoh with ⟨hstock, hC, hI, hR⟩
      refine ⟨by unfold DexState.stockExact at *; dsimp only; omega, hC, ?_, ?_⟩
      · unfold sumIns at *; dsimp only; rw [hI]
        exact sum_map_eq_sub mids (getIns st.markets) _ mid m.insurance hndM hmemM
          (by simp [getIns, updateFn, hm]) (by simp [getIns, hm])
          (fun x hx => by simp [getIns, updateFn, hx])
      · unfold sumRes at *; dsimp only; rw [hR]
        apply sum_map_update_const; intro x _
        by_cases hx : x = mid
        · subst hx; simp [getRes, updateFn, hm]
        · simp [getRes, updateFn, hx]
    · cases h

/-- Single-step relation covering EVERY balance-moving transition in `percolator-lean` v2. -/
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
  | liquidateTakeoverPostAdl {st st' mid pid liqPid rawClose feeCap loss} :
      mid ∈ mids → pid ∈ pids →
      stepLiquidateTakeoverPostAdl st mid pid liqPid rawClose feeCap loss = some st' → DexStep mids pids st st'
  | claimResolved {st st' mid pid} :
      mid ∈ mids → pid ∈ pids → stepClaimResolved st mid pid = some st' → DexStep mids pids st st'
  | sweepOrphanInsurance {st st' mid} :
      mid ∈ mids → stepSweepOrphanInsurance st mid = some st' → DexStep mids pids st st'

/-- Reflexive-transitive reachability across arbitrary multi-step transaction traces. -/
inductive DexReachable (mids pids : List Nat) : DexState → DexState → Prop where
  | refl (st : DexState) : DexReachable mids pids st st
  | step {st0 st1 st2 : DexState} :
      DexReachable mids pids st0 st1 → DexStep mids pids st1 st2 → DexReachable mids pids st0 st2

/-- **Unified Multi-Step Trace Coherence Theorem (Global No-LOF Proof!)**:
    Starting from ANY coherent DEX state `st0`, EVERY state `st` reachable via ANY finite
    interleaving of all 13 protocol transitions preserves exact aggregate coherence:
    `C_tot = ∑ capital`, `I_tot = ∑ insurance`, `R_tot = ∑ realizedPool`,
    AND `C_tot + I_tot + R_tot + S_tot = V`! -/
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
    | tradeOpenPostAdl hm hL hS h => exact tradeOpenPostAdl_preserves_coherent _ _ _ _ _ _ _ _ _ _ ih hndM hm hndP hL hS h
    | tradeReduce h => exact tradeReduce_preserves_coherent _ _ _ _ _ _ _ _ ih h
    | tradeHandoff hS hB h => exact tradeHandoff_preserves_coherent _ _ _ _ _ _ _ _ _ _ ih hndP hS hB h
    | liquidate hm hp h => exact liquidate_preserves_coherent _ _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | liquidateTakeoverPostAdl hm hp h => exact liquidateTakeoverPostAdl_preserves_coherent _ _ _ _ _ _ _ _ _ _ ih hndM hm hndP hp h
    | claimResolved hm hp h => exact claimResolved_preserves_coherent _ _ _ _ _ _ ih hndM hm hndP hp h
    | sweepOrphanInsurance hm h => exact sweepOrphanInsurance_preserves_coherent _ _ _ _ _ ih hndM hm h

/-- **Corollary (Global Multi-Step Solvency Conservation)**:
    Across ANY finite trace of protocol instructions, the exact sum of all portfolio capitals,
    all per-market insurance pools, all per-market realized pools, and global surplus equals
    the SPL vault balance `V` to the last atom! -/
theorem reachable_global_solvency (mids pids : List Nat)
    (hndM : mids.Nodup) (hndP : pids.Nodup)
    (st0 st : DexState) (h0 : st0.coherent mids pids)
    (hreach : DexReachable mids pids st0 st) :
    sumCaps st pids + sumIns st mids + sumRes st mids + st.totalSurplus = st.vault := by
  have ⟨hstock, hC, hI, hR⟩ := reachable_preserves_coherent mids pids hndM hndP st0 st h0 hreach
  unfold DexState.stockExact at hstock
  omega

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

end Percolator.TraceProofs
