# `percolator-lean` Roadmap

Prioritized list of planned improvements across trading UX, insurance & passive LPs, oracles, formal verification, and Solana production readiness.

---

## 1. Everyday Trading UX & Lazy Markets (Quick Wins)

1. **Instant PnL realization inside `Trade(mode=1)` for both sides**
   - *Current state:* `handleTrade` (`Percolator/Program.lean`) always settles `pflL` (Long) before `pflS` (Short), so a winning Long needs a trailing `RefreshLeg` to sweep `posPnl → capital` and free the empty leg slot.
   - *Improvement:* Settle the losing side first (or re-run realization on `pflL` immediately after `pflS` settles) so both Long and Short realize 100% of PnL directly into `capital` inside `Trade(mode=1)` with no trailing `RefreshLeg`.

2. **Truly lazy / dormant markets (`OI == 0`)**
   - *Current state:* `handleUpdateOracle` enforces `maxMoveBps` even when `oiLong == 0 && oiShort == 0`, and `handleStartWindDown` permits anyone to wind down a stale market after `maxStaleness` even when `OI == 0` and no trader is trapped.
   - *Improvement:*
     - Bypass `maxMoveBps` clamping in `handleUpdateOracle` when `oiLong == 0 && oiShort == 0` so dormant markets snap straight to live spot on the first trade.
     - Require `oiLong > 0 || activeLegs > 0` for permissionless stale-oracle `StartWindDown` so idle markets cannot be grief-closed after `maxStaleness`.

3. **Protocol surplus withdrawal (`ClaimSurplus`)**
   - *Current state:* `Dex.totalSurplus` accumulates rounding dust and swept orphan insurance on resolved markets, with no withdrawal path to `dex.feeVault`.
   - *Improvement:* Add an admin-gated `ClaimSurplus` instruction that transfers `Dex.totalSurplus` from `DexVault` to `dex.feeVault` while preserving exact stock equality `C + I + R + S = V`.

4. **Maker/taker fee split & optional close fees**
   - *Current state:* `tradeFeeBps` charges both sides symmetrically on `Trade(mode=0)` (opens) and `0` on `Trade(mode=1)` (closes).
   - *Improvement:* Support configurable `(takerFeeBps, makerFeeBps)` (or maker rebates) and optional close fees.

---

## 2. Insurance Fund & Passive LP Efficiency

5. **Live-market Insurance LP withdrawals**
   - *Current state:* `handleWithdrawInsurance` requires `oiLong == 0 && oiShort == 0 && rawBasis == 0` (`PErr.nonzeroOi`), preventing front-running of crashes but locking LPs on 24/7 markets where OI rarely reaches zero.
   - *Improvement:* Add either a delayed withdrawal/unbonding queue (`N`-slot cooldown request) or an excess-above-reserve withdrawal rule (`ins' ≥ minInsBps * notionalOI`) so LPs can exit healthy live markets without front-running bad-debt liquidations.

6. **Inventory-skewed `Matcher` AMM & staleness protection**
   - *Current state:* `Percolator/Matcher.lean` quotes fixed `halfSpread + impact * qty` around `markPrice`.
   - *Improvement:* Add inventory-skewed bid/ask quoting based on LP net position, an LP admin pause/parameter-update instruction, and an optional max-oracle-age guard inside `Matcher::Fill` so passive LPs are not filled against stale marks.

7. **Dedicated bankrupt-liquidation insurance backstop test**
   - *Improvement:* Add a standalone functional test in `svm-runner/src/boring_tests.rs` verifying bankrupt liquidation (`shortfall > 0`) → exact draw from `m.insurance` into `m.realizedPool` → winning counterparty paid 100% → insurance LP absorbs exact shortfall.

---

## 3. Oracles & Funding

8. **Slot-elapsed continuous funding accrual**
   - *Current state:* `OracleAdapter` computes per-crank funding per step.
   - *Improvement:* Scale funding by elapsed slots `curSlot - lastOracleSlot` (still bounded by `maxMoveBps` when `OI > 0`) so funding economics are invariant to crank cadence on lazy markets.

9. **Multi-feed median / fallback in `OracleAdapter`**
   - *Improvement:* Combine Pyth V2 + Chainlink OCR2 + Switchboard On-Demand via 2-of-3 median quoting with automatic fallback if a single oracle provider stalls.

10. **Auto-bundling client SDK (Rust / TypeScript)**
    - *Improvement:* Provide a lightweight client helper that queries active portfolio legs and builds optimal single-tx atomic bundles (`[Crank, RefreshLeg(winners)..., RefreshLeg(losers)..., Trade/Withdraw/Liquidate]`) plus a decoder for the 7 structured `sol_log_64_` event tags.

---

## 4. Formal Verification Depth

11. **Top-level handler `SvmState.mem` refinement proofs**
    - *Improvement:* Extend `Percolator/Refinement.lean` from `settleAndRefreshLeg`, `syncLegMargins`, `sweepResolvedDust`, and `applyExecSpread` to full top-level instruction handlers (`handleTrade`, `handleLiquidate`, `handleWithdrawCollateral`, `handleForceClosePair`).

12. **Wire-parser soundness proofs for `OracleAdapter`**
    - *Improvement:* Formally prove the Pyth V2, Chainlink OCR2, and Switchboard 128-bit binary parsers in `Percolator/OracleAdapter.lean` cannot overflow or read out-of-bounds on arbitrary untrusted feed bytes.

13. **End-to-end `lean-svm` compiler simulation theorem**
    - *Improvement:* Compose the 60 pass-level compiler soundness proofs in `lean-svm`'s `LeanSVM/Compiler/Proofs.lean` into a unified `SolanaM → IR → RegAlloc → sBPF` semantic preservation theorem.

---

## 5. Solana Production & Ecosystem Readiness

14. **Deterministic PDAs for `Market`, `Portfolio`, and `InsReceipt`**
    - *Improvement:* Support canonical PDA derivation (matching `DexVault`) for markets, portfolios, and insurance receipts to simplify client discovery and eliminate account lookup ambiguity.

15. **SPL Token-2022 quote mint support**
    - *Improvement:* Support Token-2022 quote mints alongside classic SPL Token while explicitly rejecting unsafe extensions (transfer fees, permanent delegate, non-zero close authority).

16. **Multi-portfolio sub-accounts & leg-count evaluation**
    - *Improvement:* Document multi-portfolio sub-accounts per wallet and evaluate bumping `MAX_LEGS` beyond 8 with v0 Address Lookup Table (ALT) transaction sizing.

17. **CI & devnet soak harness**
    - *Improvement:* Add GitHub Actions running `./scripts/build-and-test.sh` and `cargo test --release` across both repositories, plus a devnet soak setup running live Pyth Pull / Switchboard feeds, keeper bots, and AMM LPs.
