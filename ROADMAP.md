# `percolator-lean` Roadmap

Prioritized list of planned improvements across core trading & Hyperliquid-parity UX, external composable programs (Prop AMM, multi-collateral router, HLP, CLOB), oracles, formal verification, and Solana production readiness.

---

## 1. Core Trading UX & Hyperliquid Parity (`Percolator/Program.lean`)

1. **Delegated trading keys / Agent wallets (`Portfolio.tradeDelegate` + `SetDelegate`)**
   - Separate trade signing (`owner` OR `tradeDelegate`) from custody (`WithdrawCollateral`, `CloseAccount`, `SetDelegate` remain `owner`-only) to unlock 1-click browser session keys, bots, and external CLOB / TP-SL trigger programs without giving up custody.

2. **Instant PnL realization inside `Trade(mode=1)` for both sides**
   - *Current state:* `handleTrade` always settles `pflL` (Long) before `pflS` (Short), so a winning Long needs a trailing `RefreshLeg` to sweep `posPnl → capital` and free the empty leg slot.
   - *Improvement:* Settle the losing side first (or re-run realization on `pflL` immediately after `pflS` settles) so both Long and Short realize 100% of PnL directly into `capital` inside `Trade(mode=1)` with no trailing `RefreshLeg`.

3. **Truly lazy / dormant markets (`OI == 0`)**
   - *Current state:* `handleUpdateOracle` enforces `maxMoveBps` even when `oiLong == 0 && oiShort == 0`, and `handleStartWindDown` permits anyone to wind down a stale market after `maxStaleness` even when `OI == 0` and no trader is trapped.
   - *Improvement:*
     - Bypass `maxMoveBps` clamping in `handleUpdateOracle` when `oiLong == 0 && oiShort == 0` so dormant markets snap straight to live spot on the first trade.
     - Require `oiLong > 0 || activeLegs > 0` for permissionless stale-oracle `StartWindDown` so idle markets cannot be grief-closed after `maxStaleness`.

4. **Maker/taker fee split, close fees & Builder Codes (`handleTrade`)**
   - Replace symmetric open-only `tradeFeeBps` with configurable `(takerFeeBps, makerFeeBps)` (or maker rebates), optional close fees, and optional `builderPfl` capital credit inside `Trade` (zero extra SPL CPI) for third-party frontend/aggregator fee sharing.

5. **Notional-tiered margin brackets (`Market`)**
   - Add 2–3 size-based `(imBps, mmBps)` tiers so small retail positions can safely use high leverage while large whale positions carry higher maintenance margin.

6. **Protocol surplus withdrawal (`ClaimSurplus`) & on-chain `Leg.avgEntryPrice`**
   - Add an admin-gated `ClaimSurplus` instruction sweeping `Dex.totalSurplus` from `DexVault` to `dex.feeVault` while preserving exact `C + I + R + S = V`, and store `avgEntryPrice` / cost basis on `Leg` for zero-indexer wallet PnL display.

---

## 2. Insurance Fund, External Prop AMM & Composable Multi-Collateral

7. **Live-market Insurance LP withdrawals**
   - *Current state:* `handleWithdrawInsurance` requires `oiLong == 0 && oiShort == 0 && rawBasis == 0` (`PErr.nonzeroOi`), preventing front-running of crashes but locking LPs on 24/7 markets where OI rarely reaches zero.
   - *Improvement:* Add either a delayed withdrawal/unbonding queue (`N`-slot cooldown request) or an excess-above-reserve withdrawal rule (`ins' ≥ minInsBps * notionalOI`) so LPs can exit healthy live markets without front-running bad-debt liquidations.

8. **Externally-driven Prop AMM Matcher (`Percolator/Matcher.lean`)**
   - Upgrade `Matcher` to a full externally-driven Prop AMM with split `owner` (cold withdraw) vs. `quoter` (hot quote updater) authority, pushed two-sided/curve quotes `(fairPrice/bid/ask, halfSpreadBps, impactBps, skewBps, maxLongPos, maxShortPos, validUntilSlot)`, live inventory skew read from `lpPfl`, stale-quote expiry, and optional Ed25519-signed RFQ fills.

9. **Multi-Collateral UX via Atomic Swap + `1×` Covered Perp Router (Zero Core Changes!)**
   - Allow users to deposit non-quote assets (**SOL**, **jitoSOL**, **wBTC**, etc.) as cross-margin collateral in **one atomic Solana transaction** without changing core `percolator.so` or breaking `C + I + R + S = V`:
     1. Outer router / Prop AMM swaps deposited `SOL` (or LST/wBTC) for real `USDC` and deposits it into `user.Portfolio.capital` (`DepositCollateral`).
     2. Atomically opens a matching **`1×` Long `SOL/USD` perp** (`Trade(mode=0)`) against a **delta-neutral Prop AMM / HLP** holding the spot `SOL` + Short `1×` perp.
     3. Result: exact 1:1 spot-SOL price exposure, ~90% free cross-margin buying power (at 10% IM — higher than an 85% spot haircut), instant USDC PnL realization on SOL moves, zero collateral-liquidation keepers in core, and symmetric atomic close+swap back to SOL on withdrawal.
   - *(Optional later core extension if 0-funding raw spot custody is needed: native multi-vault `CollateralConfig` + permissionless keeper `ConvertCollateral`.)*

10. **External CLOB / TP-SL Trigger Orders & Multi-Depositor HLP / Copy-Trading Vaults**
    - Build standalone composable programs on top of `Portfolio.tradeDelegate` and PDA-owned `Portfolio`s for resting limit/post-only/IOC/reduce-only/TP-SL/TWAP orders and pooled multi-depositor HLP / copy-trading vaults executing `Liquidate(mode=1)` takeovers.

11. **Dedicated bankrupt-liquidation insurance backstop test**
    - Add a standalone functional test in `svm-runner/src/boring_tests.rs` verifying bankrupt liquidation (`shortfall > 0`) → exact draw from `m.insurance` into `m.realizedPool` → winning counterparty paid 100% → insurance LP absorbs exact shortfall.

---

## 3. Oracles & Funding

12. **Slot-elapsed continuous funding accrual**
    - *Current state:* `OracleAdapter` computes per-crank funding per step.
    - *Improvement:* Scale funding by elapsed slots `curSlot - lastOracleSlot` (still bounded by `maxMoveBps` when `OI > 0`) so funding economics are invariant to crank cadence on lazy markets.

13. **Multi-feed median / fallback in `OracleAdapter`**
    - *Improvement:* Combine Pyth V2 + Chainlink OCR2 + Switchboard On-Demand via 2-of-3 median quoting with automatic fallback if a single oracle provider stalls.

14. **Auto-bundling client SDK (Rust / TypeScript)**
    - *Improvement:* Provide a lightweight client helper that queries active portfolio legs and builds optimal single-tx atomic bundles (`[Crank, RefreshLeg(winners)..., RefreshLeg(losers)..., Trade/Withdraw/Liquidate]`) plus a decoder for the 7 structured `sol_log_64_` event tags.

---

## 4. Formal Verification Depth

15. **Top-level handler `SvmState.mem` refinement proofs**
    - *Improvement:* Extend `Percolator/Refinement.lean` from `settleAndRefreshLeg`, `syncLegMargins`, `sweepResolvedDust`, and `applyExecSpread` to full top-level instruction handlers (`handleTrade`, `handleLiquidate`, `handleWithdrawCollateral`, `handleForceClosePair`).

16. **Wire-parser soundness proofs for `OracleAdapter`**
    - *Improvement:* Formally prove the Pyth V2, Chainlink OCR2, and Switchboard 128-bit binary parsers in `Percolator/OracleAdapter.lean` cannot overflow or read out-of-bounds on arbitrary untrusted feed bytes.

17. **End-to-end `lean-svm` compiler simulation theorem**
    - *Improvement:* Compose the 60 pass-level compiler soundness proofs in `lean-svm`'s `LeanSVM/Compiler/Proofs.lean` into a unified `SolanaM → IR → RegAlloc → sBPF` semantic preservation theorem.

---

## 5. Solana Production & Ecosystem Readiness

18. **Deterministic PDAs for `Market`, `Portfolio`, and `InsReceipt`**
    - *Improvement:* Support canonical PDA derivation (matching `DexVault`) for markets, portfolios, and insurance receipts to simplify client discovery and eliminate account lookup ambiguity.

19. **SPL Token-2022 quote mint support**
    - *Improvement:* Support Token-2022 quote mints alongside classic SPL Token while explicitly rejecting unsafe extensions (transfer fees, permanent delegate, non-zero close authority).

20. **Multi-portfolio sub-accounts & leg-count evaluation**
    - *Improvement:* Document multi-portfolio sub-accounts per wallet and evaluate bumping `MAX_LEGS` beyond 8 with v0 Address Lookup Table (ALT) transaction sizing.

21. **CI & devnet soak harness**
    - *Improvement:* Add GitHub Actions running `./scripts/build-and-test.sh` and `cargo test --release` across both repositories, plus a devnet soak setup running live Pyth Pull / Switchboard feeds, keeper bots, and AMM LPs.
