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
| **Minimum Nonzero MM Floor** | `minMm_strengthens_solvency` | Enforcing $\text{MM} = \max(\text{minMm}, \text{marginReq}(N, \text{mmBps}))$ strictly strengthens `oracle_clamp_zero_bad_debt` while preventing dust-liquidation griefing. |
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
| **Authority Rotation Isolation** | `updateMarketAuth_zero_contagion`, `tombstone_rejects_updateMarketAuth` | Rotating `oracleAuth` or transferring/burning `marketAdmin` preserves exact global stock equality and leaves balances, OI, portfolios, and other markets untouched; permanently rejected on tombstoned markets. |

---

## 5. Fair Liquidations, Anti-Selective-Liquidation, Post-ADL Recovery, Position Hand-Off & Exit-Liveness

| Invariant | Lean 4 Theorem | Guarantee |
|---|---|---|
| **Anti-Selective-Liquidation (All-Leg Freshness)** | `hedged_portfolio_immune_to_selective_liquidation` | `Liquidate` unconditionally rejects if ANY active leg on the portfolio was not refreshed in `curSlot`, and unconditionally rejects once all legs are fresh and `cap1 + pnl1 ≥ totalMm` with `shortfall = 0` — hedged cross-margin spreads cannot be selectively liquidated without crediting winning legs. |
| **Fair Gradual Liquidation Fee** | `gradualLiqFee_bounded`, `proportionalOiForRaw_preserves_oi_le_raw` | `gradualLiqFee(maxFee, deficit)` stays strictly in `[min(maxFee, maxFee/4), maxFee]`, and ceiling proportional OI reduction preserves `oi' ≤ raw'` unconditionally even on 1-atom post-ADL dust. |
| **Counterparty Takeover (Zero ADL & Post-ADL Safe)** | `liquidateTakeover_sound`, `liquidateTakeoverPostAdl_sound` | `Liquidate(mode=1)` transfers `rawClose` within the same side, preserving `stockExact`, `m'.wf`, victim `otherMm` containment, cross-market isolation, and leaving `oiLong/Short`, `rawBasisLong/Short`, and `adlLong/Short` bit-for-bit invariant — even during active partial ADL! |
| **Post-ADL Monotone Opens** | `postAdlRawAdd_ge_qty`, `postAdlOpen_preserves_adl_monotone`, `tradeOpenPostAdl_sound` | Opening `qty` on a partially-ADL'd side (`0 < oi ≤ raw`) mints `rAdd = max(qty, ⌈qty · raw / oi⌉)`, guaranteeing `oi + qty ≤ raw + rAdd`, `(oi + qty) · raw ≤ oi · (raw + rAdd)`, and `deriveAdl(oi + qty, raw + rAdd) ≤ deriveAdl(oi, raw)` — never inflating any existing holder's effective position. |
| **Same-Side Position Hand-Off** | `tradeHandoff_sound` | `Trade(mode=2/3)` transfers `rawXfer` between two portfolios on the same side (`Long→Long` or `Short→Short`), preserving `stockExact`, leaving the entire `MarketState` (`oi`, `rawBasis`, `adl`) bit-for-bit invariant, and leaving all untouched portfolios unchanged. |
| **Spread-Protected Reduce** | `tradeReduceWithSpread_sound` | Paying an `execPrice` spread during `Trade(mode=1)` reduce preserves `stockExact`, `m'.wf`, and `capital' ≥ newTotalMm`. |
| **Closed Inductive Aggregate Coherence** | `depositCollateral_preserves_coherent`, `withdrawCollateral_preserves_coherent`, `realizeLegPnl_preserves_coherent` | Inductively preserves exact finite-sum coherence `C_tot = ∑ capital`, `I_tot = ∑ insurance`, `R_tot = ∑ realizedPool`, and `C_tot + I_tot + R_tot + S_tot = V`. |
| **Anti-DoS Exit-Liveness** | `flat_portfolio_unconditionally_withdrawable`, `market_bounded_exit_liveness` | Flat portfolios can unconditionally withdraw 100% of capital at any slot; every well-formed market has bounded permissionless exit deadlines (`maxStaleness ≤ 9,000`, `exitWindow ≤ 216,000`). |

---

## 6. External Composable Program Proofs

| Program | Lean 4 Theorems | Guarantee |
|---|---|---|
| **[`Percolator.Matcher`](Percolator/Matcher.lean)** | `quoteAsk_ge_mark`, `quoteBid_le_mark`, `quoteAsk_within_maxMove`, `quoteBid_within_maxMove` | Passive LP AMM ask quotes are always $\ge \text{markPrice}$, bid quotes are always $\le \text{markPrice}$, and both stay strictly within `±⌊markPrice * maxMoveBps / 10000⌋` (guaranteed to satisfy core `execPriceClamp`). |
| **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** | `crank_step_and_funding_within_clamp` | Auto-clamped price convergence step plus on-chain premium funding always satisfy $|\Delta P| + \text{fundE6} \le \lfloor P_{\text{old}} \cdot \text{maxMoveBps} / 10000 \rfloor$. |

---

## 7. Runtime Boundary Checks Enforced On-Chain (`Percolator/Program.lean`)

Beyond the pure mathematical transitions, the compiled sBPF program enforces the Solana execution boundary:

1. **Canonical Program Pinning:** All SPL CPIs require exact 32-byte match with `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`, and `InitDex` pins `SystemProgram` (`11111111111111111111111111111111`).
2. **On-Chain `DexVault` PDA Creation & Integrity:** `InitDex` creates and initializes `vaultPda` on-chain via `SystemProgram::Transfer + Allocate + Assign` (signed by PDA `["dvlt", dex, bump]`) + `SPL Token InitializeAccount3`, cryptographically enforcing PDA derivation, clean zero-balance SPL state, no delegate, no close authority, and immunity to 1-lamport pre-funding griefing.
3. **Per-Slot Oracle Rate Limit:** `UpdateOracle` enforces `curSlot > lastOracleSlot`, ensuring single-step clamped moves per slot.
4. **Same-Slot Multi-Leg Freshness:** `WithdrawCollateral`, `Trade(mode=0)`, buyer legs in `Trade(mode=2/3)`, and `Liquidate` enforce `leg.lastRefreshSlot == curSlot` for every active open leg, preventing both stale-oracle collateral extraction and selective single-leg liquidation of hedged spreads while keeping flat withdrawals unconditional.
5. **Post-ADL Insurance, Resolution & Safe Rent Reclaim:** `WithdrawInsurance` requires `oiLong == 0 ∧ oiShort == 0 ∧ rawBasisLong == 0 ∧ rawBasisShort == 0`; `ResolveMarket` additionally requires `activeLegs == 0`; `CloseAccount` only closes empty `Portfolio`/`InsReceipt` or `Tombstoned` `Market` and zeroes the magic word before draining lamports to prevent same-tx revival.
