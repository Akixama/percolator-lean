# `percolator-lean` Formal Invariants & Proof Catalog

Every economic, solvency, and risk-isolation invariant of `percolator-lean` is formalized in [`Percolator/Spec.lean`](Percolator/Spec.lean) and machine-checked in Lean 4's kernel in [`Percolator/Proofs.lean`](Percolator/Proofs.lean) with **0 `sorry`**, **0 custom axioms**, and **0 external Lean dependencies**.

---

## 1. Exact Global Stock Equality & Haircut Conservation

| Invariant | Lean 4 Theorem | Guarantee |
|---|---|---|
| **Global Stock Equality** | `createMarket_sound`, `depositCollateral_sound`, `withdrawCollateral_sound`, `depositInsurance_sound`, `withdrawInsurance_sound`, `realizeLegPnl_sound`, `settleContainedLoss_sound`, `tradeOpen_sound`, `tradeReduce_sound`, `liquidate_sound`, `clearDeadLeg_sound`, `forceClosePair_terminates_and_sound`, `claimResolved_sound` | Every transition preserves exact disjoint partitioning $C_{\text{tot}} + I_{\text{tot}} + R_{\text{tot}} + S_{\text{tot}} = V$ with zero token creation, leakage, or cross-class drift. |
| **Face-Value Cap** | `haircutPayout_le_face` | $\text{haircutPayout}(p, R_m, P^+_m) \le p$: no claimant can receive more than their face positive PnL. |
| **Isolated Backing Cap** | `haircutPayout_le_residual` | $p \le P^+_m \implies \text{haircutPayout}(p, R_m, P^+_m) \le R_m$: payouts on market $m$ are strictly bounded by market $m$'s own realized loser pool $R_m$. |
| **No First-Mover Drain** | `haircutPayout_monotone_ratio` | $(R_m - \text{pay}) \cdot P^+_m \ge R_m \cdot (P^+_m - p)$: floor division strictly preserves or improves the backing ratio for all remaining claimants. |
| **Finite-Sum Non-Over-Subscription** | `sum_mul_div_le`, `sum_resolved_payouts_le_realizedPool` | For any finite list of claimants with $\sum p_i \le \text{resolvedDen}$ and $\text{resolvedNum} \le R_m$, $\sum_i \text{resolvedLegPayout}(m, p_i) \le R_m$: the resolved pool can never be over-subscribed regardless of claim count or rounding. |
| **Order Independence** | `resolved_payout_order_independent` | In `Resolved` status, each winner's payout depends strictly on the immutable snapshot `(resolvedNum, resolvedDen)` and is independent of claim order. |

---

## 2. Cross-Margin Isolation Envelope & Clamped Oracle Solvency

| Invariant | Lean 4 Theorem | Guarantee |
|---|---|---|
| **Clamped Oracle Zero Bad Debt** | `oracle_clamp_zero_bad_debt` | Under the market solvency envelope $\text{maxMoveBps} + \text{liqFeeBps} \le \text{mmBps}$ and oracle clamp $|\Delta P| \cdot 10^4 \le P_{\text{old}} \cdot \text{maxMoveBps}$, any healthy position ($\text{equity} \ge \text{MM}$) satisfies $\text{stepLoss} + \text{liqFee} \le \text{equity}$ — zero bad debt and zero insurance theft on single-step moves. |
| **Cross-Margin Isolation Envelope** | `cross_margin_isolation_envelope` | Simultaneously proves **both** halves of cross-margin containment for `applyContainedLoss` with `capAvailableForLeg = capital - (totalMm - leg.cachedMm)`: (1) **Anti-Reverse-Contagion:** any loss $L$ on a toxic leg leaves $\text{capital}' \ge \text{totalMm} - \text{leg.cachedMm}$, preserving maintenance margin for every other leg; (2) **Anti-Shielding:** whenever $\text{capital} \ge \text{totalMm}$, no other leg can shield `capital` from paying a healthy market's clamped 1-step loss + liquidation fee. |
| **Zero-Sum Oracle Step** | `oracle_step_zero_sum` | Directional rounding guarantees credited winner delta $\lfloor A \cdot \Delta / 10^9 \rfloor \le \lceil A \cdot \Delta / 10^9 \rceil$ debited loser delta on every oracle tick. |

---

## 3. Open Interest, Derived ADL & Termination

| Invariant | Lean 4 Theorem | Guarantee |
|---|---|---|
| **Derived ADL Bound** | `deriveAdl_le_one` | $A_{\text{side}} = \text{deriveAdl}(\text{OI}, \text{rawBasis}) \le 10^9$ unconditionally. |
| **Effective Exposure Bound** | `deriveAdl_exposure_le_oi` | $\text{effectiveQty}(\text{rawBasis}, \text{deriveAdl}(\text{OI}, \text{rawBasis})) \le \text{OI}$ whenever $0 < \text{rawBasis} \le 10^9 \cdot \text{OI}$: ADL-adjusted exposure never exceeds live open interest. |
| **Balanced OI & Well-Formedness** | `createMarket_sound`, `tradeOpen_sound`, `tradeReduce_sound`, `liquidate_sound`, `clearDeadLeg_sound`, `forceClosePair_terminates_and_sound` | Every market transition preserves `oiLong == oiShort <= maxOi`, `oiSide <= rawBasisSide`, `adlSide <= ADL_ONE`, and the solvency envelope. |
| **Wind-Down Termination** | `forceClosePair_terminates_and_sound` | Each `ForceClosePair` call strictly decreases both `oiLong` and `oiShort` ($m'.\text{oiLong} < m.\text{oiLong}$ and $m'.\text{oiShort} < m.\text{oiShort}$), guaranteeing finite termination to `OI = 0`. |

---

## 4. Cross-Market, Insurance & Governance Isolation

| Invariant | Lean 4 Theorem | Guarantee |
|---|---|---|
| **Per-Market & Untouched-User Frame Isolation** | `createMarket_sound`, `depositCollateral_sound`, `withdrawCollateral_sound`, `depositInsurance_sound`, `withdrawInsurance_sound`, `realizeLegPnl_sound`, `settleContainedLoss_sound`, `tradeOpen_sound`, `tradeReduce_sound`, `liquidate_sound`, `clearDeadLeg_sound`, `forceClosePair_terminates_and_sound`, `claimResolved_sound` | Every transition on market $m$ and portfolio(s) $p$ proves `st'.markets otherMid = st.markets otherMid` for all $\text{otherMid} \ne m$ and `st'.portfolios otherPid = st.portfolios otherPid` for all untouched portfolios $\text{otherPid} \ne p$. |
| **Zero Admin Custody / Contagion** | `admin_updateCreateFee_zero_contagion` | Protocol admin fee updates leave `stockExact`, `markets`, `portfolios`, and `insShares` identically unchanged. |
| **Terminal Tombstone Permanence** | `tombstone_rejects_burnAdmin` | Tombstoned markets reject state-mutating instructions permanently. |

---

## 5. Runtime Boundary Checks Enforced On-Chain (`Percolator/Program.lean`)

Beyond the pure mathematical transitions, the compiled sBPF program enforces the Solana execution boundary:

1. **Canonical Token Program Pinning:** All SPL CPIs require exact 32-byte match with `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`.
2. **Cryptographic Vault PDA & SPL Account Integrity:** `InitDex` verifies `sol_sha256(["dvlt", dex, bump, progId, "ProgramDerivedAddress"]) == vaultPda` and asserts SPL owner, mint, self-ownership, 0 initial balance, `Initialized` state, no delegate, and no close authority.
3. **Per-Slot Oracle Rate Limit:** `UpdateOracle` enforces `curSlot > lastOracleSlot`, ensuring single-step clamped moves per slot.
4. **Same-Slot Multi-Leg Freshness:** `WithdrawCollateral` and `Trade(mode=0)` enforce `leg.lastRefreshSlot == curSlot` for every active open leg, preventing stale-oracle collateral extraction while keeping flat withdrawals unconditional and `Liquidate` strictly $O(1)$.
5. **Post-ADL Insurance & Resolution Lock:** `WithdrawInsurance` requires `oiLong == 0 ∧ oiShort == 0 ∧ rawBasisLong == 0 ∧ rawBasisShort == 0`; `ResolveMarket` additionally requires `activeLegs == 0`.
