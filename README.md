# `percolator-lean` — Formally Verified Realizable Cross-Margin Perpetuals DEX on Solana

`percolator-lean` is a minimal, composable, formally verified Solana perpetuals DEX written in **Lean 4** and compiled directly to zero-heap Solana sBPF bytecode via [`lean-svm`](https://github.com/aeyakovenko/lean-svm).

It achieves **full cross-margin capital efficiency on healthy markets** (hedged spreads net 1:1 with zero warmup drag) while maintaining **machine-checked per-market risk isolation**: permissionlessly created or adversarial markets cannot drain other markets, untouched users, or other markets' insurance pools.

The repository ships a minimal core clearinghouse ([`percolator.so`](Percolator/Program.lean)) plus two tiny, formally verified composable external programs that integrate via CPI without bloating the core:
- **[`Percolator.Matcher`](Percolator/Matcher.lean)** (`8,552 B`) — permissionless passive-LP AMM / spread matcher enabling single-signer taker opens & closes against resting PDA-owned LP portfolios.
- **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** (`18,504 B`) — permissionless on-chain oracle bridge natively parsing **Pyth Pull (`PriceUpdateV2`)**, **Chainlink OCR2 (`Transmissions`)**, **Switchboard On-Demand (`PullFeedAccountData`, 128-bit `PRECISION=18`)**, custom feeds, **2-leg composite ratios** (`base / quote`, e.g. `STOXX/SOL`), and **EWMA smoothing + Hybrid After-Hours mode** (carrying `ewmaPrice` while cash markets are closed, still repricing 24/7 against a live quote feed, plus optional per-slot bounded `PushEwmaMark`), with pinned feed owners/IDs, confidence & staleness checks, smooth multi-slot auto-clamped convergence, and on-chain premium funding.

| Program | ELF `.so` Size | sBPF Insns | Stack | Heap | Formal Lean 4 Proofs (`0 sorry`, `0` custom axioms) |
|---|---:|---:|---:|---:|---|
| **[`Percolator.Program`](Percolator/Program.lean)** (Core DEX) | **65,760 B** | 8,069 | 424 B | 0 B | 66 theorems (`Proofs.lean` + `TraceProofs.lean`) |
| **[`Percolator.Matcher`](Percolator/Matcher.lean)** (LP AMM CPI) | **8,552 B** | 949 | 712 B | 0 B | 4 theorems (`quoteAsk/Bid` bounds & clamp) |
| **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** (Pyth/CL/SB + Ratio + EWMA CPI) | **18,504 B** | 2,187 | 552 B | 0 B | 7 theorems (`crank_step_and_funding_within_clamp`, `ringBufferPrevIdx_lt`, `scaleToE6Nat_mono_and_id`, `ratio_crank_within_clamp`, `ewmaBlendNat_bounds`, `ewmaBlendNat_fixed_point`, `ewma_ratio_crank_within_clamp`) |

---

## 1. Architecture & Composability

```
┌─────────────────────────────────┐     ┌──────────────────────────────────┐
│  Percolator.Matcher (8,552 B)   │     │ Percolator.OracleAdapter         │
│  • Passive LP AMM / Spreads     │     │ (18,504 B)                       │
│  • Single-Signer Taker Fill     │     │ • Pyth V2 / Chainlink / SB 128b  │
│  • PDA-Owned LP Portfolio       │     │ • 2-Leg Ratios + EWMA/AfterHours │
└───────────────┬─────────────────┘     └───────────────┬──────────────────┘
                │ CPI (invoke_signed)                   │ CPI (invoke_signed)
                ▼  InitPortfolio / Trade / Withdraw     ▼  UpdateOracle
┌──────────────────────────────────────────────────────────────────────────┐
│                percolator-lean Core (65,760 B · 20 ops · 0 heap)         │
│  • Realizable Shared Cross-Margin      • On-Chain PDA Vault Creation     │
│  • Per-Market Isolated R_m / I_m / A_m • Exact C + I + R + S = V         │
│  • Fair Partial Takeover & Hand-Off    • Post-ADL Monotone Recovery      │
│  • Bounded execPrice Spreads           • Zero-Heap sol_log_64_ Events    │
└──────────────────────────────────────────────────────────────────────────┘
```

Keeping matching, AMM quoting, orderbooks, external oracle parsing, funding formulas, and collateral swaps in external composable programs keeps the core clearinghouse tiny, auditable, and immutable:
- Any external program (CLOB, AMM, RFQ, vault, router) can own a `Portfolio` via its PDA, accept permissionless collateral deposits via `DepositCollateral`, and execute fills via `Trade` with an oracle-clamped `execPrice` spread.
- Any external oracle bridge (Pyth, Switchboard, Chainlink, TWAP, funding calculator) can hold `Market.oracleAuth` via its PDA and crank `UpdateOracle`.

---

## 2. Core Protocol Design

### 2.1 Realizable Shared Cross-Margin & Exact Stock Equality

1. **One shared quote custody vault (`DexVault` PDA `["dvlt", dex]`)**, created and initialized directly on-chain by `InitDex` via `SystemProgram::Transfer + Allocate + Assign + SPL Token InitializeAccount3` (immune to 1-lamport pre-funding griefing and ready for devnet/mainnet with zero external setup).
2. **Exact four-class accounting partition:**
   $$C_{\text{tot}} + I_{\text{tot}} + R_{\text{tot}} + S_{\text{tot}} = V$$
   where $C_{\text{tot}} = \sum_p \text{capital}_p$ (shared portfolio collateral), $I_{\text{tot}} = \sum_m I_m$ (per-market isolated insurance), $R_{\text{tot}} = \sum_m R_m$ (per-market isolated realized loser pools), $S_{\text{tot}} = \sum_m S_m$ (rounding sinks), and $V$ is the exact SPL Token balance of `DexVault`.
3. **Instant backed profit realization:** Positive PnL on market $m$ (`posPnl`) is a claim strictly against market $m$'s own `realizedPool` $R_m$. On healthy markets ($R_m \ge P^+_m$ with `warmupSlots == 0`), `RefreshLeg` immediately credits `posPnl` **1:1 into shared `pfl.capital`** ($R_m \to C_{\text{tot}}$). Hedged multi-market portfolios (e.g. Long $500 BTC + Short $500 ETH on $100 shared capital) net 1:1 in a single atomic transaction `[RefreshLeg(ETH), RefreshLeg(BTC)]` with zero liquidation and zero warmup drag.
4. **Insolvent haircut conservation:** When $R_m < P^+_m$, positive PnL payout is strictly bounded by floor division $\lfloor p \cdot \min(R_m, P^+_m) / P^+_m \rfloor \le \min(p, R_m)$, proven monotone non-decreasing for remaining claimants (`haircutPayout_monotone_ratio` — no first-mover drain).

### 2.2 Per-Leg Loss Containment & `reservedMm` Anti-Shielding Firewall

Each `Portfolio` maintains `totalMm = ∑ active_leg.cachedMm`, `totalIm = ∑ active_leg.cachedIm`, and `totalReservedMm = ∑ active_leg.reservedMm` with the unconditional inductive invariant **`totalReservedMm ≤ capital`**. When leg $j$ incurs a loss or liquidation fee, debits from shared `capital` are strictly capped at:

$$\text{capAvailableForLeg}(j) = \text{capital} - (\text{totalReservedMm} - \text{leg}_j.\text{reservedMm})$$

On every margin refresh (`syncLegMargins`), a leg may only grow `reservedMm` above its prior reservation when `capital ≥ totalMm'` (and always bounded by `capital - otherRes`). This proves both halves of `cross_margin_isolation_envelope` AND `alice_mule_godmode_rug_zero_haircut_on_bob`:
- **Anti-Reverse-Contagion:** Even an arbitrarily large crash on a toxic leg (`RUG/USD`) leaves $\text{capital}' \ge \text{otherRes}$, protecting unrelated healthy legs (`BTC`, `ETH`, `SOL`) and keeping their insurance pools bit-for-bit untouched.
- **Unconditional Anti-Shielding (God-Mode `RUG` Oracle Immunity):** Even if Alice + Mule control `RUG/USD`'s oracle and pump `RUG/USD` 12×+ (Long or Short `RUG`) to inflate `rugLeg.cachedMm ≫ capital`, `totalReservedMm ≤ capital` holds unconditionally and `solLeg.reservedMm` is never reduced — guaranteeing $\text{capAvailableForLeg}(\text{SOL}) \ge \text{MM}_{\text{SOL}}$ so Bob's `SOL/USD` payout suffers **zero shortfall, zero insurance draw, and zero haircut**, while preserving 100% full cross-margin sharing of excess equity on healthy markets.

Each market may also set an immutable nonzero maintenance-margin floor `minMm` (`computeMarginWithFloor`), eliminating dust-position liquidation griefing while strictly strengthening solvency (`minMm_strengthens_solvency`).

### 2.3 Same-Slot Multi-Leg Freshness & Anti-Selective-Liquidation

- `RefreshLeg(dex, mkt, pfl)` is $O(1)$ and permissionless: verifies fresh oracle (on `Active` markets; works unconditionally during `WindDown`), settles `entryK → kSide`, realizes backed `posPnl`, updates `cachedMm`/`cachedIm`, and stamps `leg.lastRefreshSlot = curSlot`.
- `WithdrawCollateral`, risk-increasing `Trade(mode=0)`, buyer legs in `Trade(mode=2/3)`, and **`Liquidate`** all enforce `leg.lastRefreshSlot == curSlot` across every active open leg on the portfolio (`hedged_portfolio_immune_to_selective_liquidation`).
  - Prevents stale-oracle collateral extraction AND prevents selective single-leg liquidation of a net-healthy hedged cross-margin spread without first crediting winning legs.
  - Even in the worst case (`MAX_LEGS = 8` on BOTH parties = 16 legs), `[16× RefreshLeg + Trade]` or `[14× RefreshLeg + Liquidate(mode=1)]` fits inside **one single legacy Solana transaction** (`≤ 876 B / 1,232 B`, `≤ 20,068 CU`).
  - Flat portfolios withdraw unconditionally (`flat_portfolio_unconditionally_withdrawable`).

### 2.4 Fair Transparent Liquidations (No TTP), Post-ADL Recovery & Position Hand-Off

- **Zero trusted liquidation oracle:** Liquidations require no TTP — solvency, partial sizing, and ADL haircuts derive purely from on-chain mark prices and exact `oiLong == oiShort` vs `rawBasis` ratios.
- **Gradual deficit-scaled fee & partial liquidations:** `Liquidate` supports partial (`reqQty > 0`, respecting `minMm` dust floor) or full closes, with a fair deficit-scaled fee `min(maxFee, max(maxFee/4, deficit))` strictly bounded above `otherMm` (anti-reverse-contagion).
- **Tiered takeover before ADL (`mode=1`):** Any well-collateralized counterparty or HLP vault can take over a distressed leg at mark (`mode=1`) with **zero OI destruction and zero ADL**, leaving `oiSide`, `rawBasisSide`, and `adlSide` bit-for-bit invariant — and working **even during active partial ADL** (`liquidateTakeoverPostAdl_sound`).
- **Tier-3 fallback & post-ADL monotone recovery:** When no taker steps in (`mode=0`), `Liquidate` symmetrically reduces `oiLong`/`oiShort` using ceiling proportional OI removal (`proportionalOiForRawU64`) and updates `adlSide = deriveAdl(oi, rawBasis)`. Markets with `0 < oiSide < rawBasisSide` remain open for new bilateral trades (`Trade mode=0`) by minting `rawAdd = max(qty, ⌈qty · rawSide / oiSide⌉)` (`postAdlOpen_preserves_adl_monotone`), never inflating any existing holder's effective position. Only 100%-wiped-out sides (`oiSide == 0 ∧ rawSide > 0`) wait for permissionless `ClearDeadLeg` to reset `adlSide → ADL_ONE`.
- **Same-side position hand-off (`Trade` `mode=2` Long→Long, `mode=3` Short→Short):** Any position holder can directly transfer part or all of a Long or Short leg to a new holder (with optional bounded `execPrice` spread) in both `Active` and `WindDown` states, leaving `oiLong`, `oiShort`, `rawBasisLong`, `rawBasisShort`, and `adlLong/Short` bit-for-bit invariant (`tradeHandoff_sound`).
- **Bounded permissionless lifecycle:** Market creation caps `maxStaleness ≤ 9,000` (~1h) and `exitWindow ≤ 216,000` (~24h) (`market_bounded_exit_liveness`), and enforces `warmupSlots == 0`. `Active` → `WindDown` (admin or permissionless on stale oracle) → `ForceClosePair` (permissionless after `exitWindow`) → `ResolveMarket` (once `oi = rawBasis = activeLegs = 0`) → `ClaimResolved` (order-independent payout) → `TombstoneMarket` → `CloseAccount` (reclaims 100% rent).

---

## 3. Account Layouts

| Account | Magic | Size | Key Fields |
|---|---|---:|---|
| **`Dex`** | `PDEX` | 200 B | `admin`, `quoteMint`, `vaultPda`, `vaultBump`, `decimals`, `feeVault`, `createFee`, `vaultBalance (V)`, `totalCapital`, `totalInsurance`, `totalResidual`, `totalSurplus` |
| **`Market`** | `MKTP` | 352 B | `status`, `marketId`, `dex`, `oracleAuth`, `marketAdmin`, `markPrice`, `lastOracleSlot`, `windDownSlot`, immutable risk params (`imBps`, `mmBps`, `liqFeeBps`, `tradeFeeBps`, `maxMoveBps`, `maxInsDrawBps`, `maxOi`, `exitWindow`, `maxStaleness`, `warmupSlots`, `minMm`), `realizedPool`, `insurance`, `feeSurplus`, `totalPosPnl`, `oiLong/Short`, `rawBasisLong/Short`, `adlLong/Short`, `kLong/Short`, `resolvedNum/Den`, `activeLegs` |
| **`Portfolio`** | `PFLO` | 880 B | 112 B header (`legCount`, `portfolioId`, `episode`, `dex`, `owner`, `capital`, `totalMm`, `totalIm`) + **8 × 96 B `Leg` slots** |
| **`InsReceipt`** | `INSR` | 88 B | `marketId`, `owner`, `market`, `shares` |

---

## 4. Core Instruction Set (20 Minimal Instructions)

| Op | Instruction | Purpose |
|---:|---|---|
| 0 | `InitDex` | Initialize `Dex` and create/initialize `DexVault` PDA on-chain (`Transfer + Allocate + Assign + InitializeAccount3`) |
| 1 | `UpdateCreateFee` | Update future `createFee` (`<= MAX_CREATE_FEE`) and optionally rotate `dex.admin` |
| 2 | `CreateMarket` | Permissionlessly create isolated market enforcing solvency envelope & optional `minMm` floor |
| 3 | `UpdateMarketAuth` | Transfer or permanently burn `marketAdmin` (`role=0`), or rotate `oracleAuth` (`role=1`) |
| 4 | `UpdateOracle` | Rate-limited (`curSlot > lastOracleSlot`), clamped mark price + funding step |
| 5 | `InitPortfolio` | Initialize 8-leg shared cross-margin portfolio (EOA or external program PDA owner) |
| 6 | `DepositCollateral` | Permissionlessly deposit quote SPL tokens into any portfolio's shared `capital` |
| 7 | `WithdrawCollateral` | Owner-signed withdrawal enforcing same-slot leg freshness + `cap' >= totalIm` |
| 8 | `DepositInsurance` | Mint isolated LP shares for `I_m`, or permanently donate (`donate=1`, 0 shares minted) |
| 9 | `WithdrawInsurance` | Burn LP shares for pro-rata `I_m` (requires `OI == 0 ∧ rawBasis == 0`) |
| 10 | `RefreshLeg` | Permissionless $O(1)$ settle, backed `posPnl` realization, margin sync & slot stamp |
| 11 | `Trade` | Bilateral open (`mode=0`, post-ADL safe), proportional reduce (`mode=1`), or same-side position hand-off (`mode=2` L→L, `mode=3` S→S) with optional clamped `execPrice` spread |
| 12 | `Liquidate` | Permissionless partial/full liquidation with all-leg freshness, gradual deficit fee, per-leg loss containment, post-ADL-safe counterparty takeover (`mode=1`), and capped `I_m` + derived ADL fallback (`mode=0`) |
| 13 | `ClearDeadLeg` | Permissionlessly clear zero-OI post-ADL leg & reset `adlSide → ADL_ONE` |
| 14 | `StartWindDown` | Admin or permissionless stale-oracle transition to `WindDown` |
| 15 | `ForceClosePair` | Permissionless post-`exitWindow` forced bilateral close |
| 16 | `ResolveMarket` | Snapshot immutable pro-rata payout ratio once `oi = rawBasis = activeLegs = 0` |
| 17 | `ClaimResolved` | Order-independent pro-rata claim from `R_m` into shared `pfl.capital` |
| 18 | `TombstoneMarket` | Permanently seal drained market (`I_m = 0 ∧ P^+_m = 0`) |
| 19 | `CloseAccount` | Unified rent reclaim for empty `Portfolio`, empty `InsReceipt`, or `Tombstoned` `Market` |

---

## 5. Structured Zero-Heap Event Logs (`sol_log_64_`)

Key state transitions emit compact structured 5×`u64` logs via Solana's `sol_log_64_` syscall (**0 heap, 0 `.rodata`, ~100 CU**):

| Tag | Event | Payload `(arg0, arg1, arg2, arg3, arg4)` |
|---:|---|---|
| `1` | `Oracle` | `(1, marketId, newPrice, fundSign, fundE6)` |
| `2` | `Trade` | `(2, (marketId << 8) \| mode, qty, execPrice, markPrice)` |
| `3` | `Liquidate` | `(3, (marketId << 8) \| mode, rawClose, liqFee, shortfall)` |
| `4` | `Deposit` | `(4, portfolioId, amount, newCapital, 0)` |
| `5` | `Withdraw` | `(5, portfolioId, amount, newCapital, 0)` |
| `6` | `ForceClose` | `(6, marketId, closedQty, remainingOi, slot)` |
| `7` | `Resolve` | `(7, marketId, resolvedNum, resolvedDen, 0)` |

---

## 6. Atomic Transaction Bundling & `T`-Slot Adversarial-Leader Requirements

Because `percolator-lean` eliminates monolithic $O(N)$ global slabs in favor of $O(1)$ per-leg instructions (`≤ 19.4k CU` worst-case), every actor composes multi-instruction operations inside **one single atomic Solana transaction** (zero multi-slot atomicity required — 1 honest leader every `T` slots is always sufficient).

### Required Atomic Transaction Bundles (by Actor)

| Actor & Operation | Required Atomic Instruction Order (Single Solana Tx) | Worst-Case CU | Legacy Wire Size | Why Order Matters |
|---|---|---:|---:|---|
| **Oracle / Crank Bot** *(Anti-Reordering Standard)* | `[OracleAdapter::Crank(m), RefreshLeg(m, lp_portfolio)]` *(repeat per market in same tx)* | **6,715 CU** *(2 mkts)* | **552 B** / 1,232 B | Funds `R_m` from losing LP counterparties in the **same tx** that moves mark price, leaving zero slot/ordering window for adversarial leaders to prematurely liquidate hedged spreads before `R_m` fills. |
| **Trader — Open / Increase** | `[RefreshLeg(m_i, taker)... , RefreshLeg(m_j, maker)... , Trade(mode=0)]` *(refresh winning legs BEFORE losing legs)* | **19,361 CU** *(16 legs)* | **865 B** / 1,232 B | Satisfies same-slot freshness (`lastRefreshSlot == curSlot`) on all open legs of both parties; refreshing winners first credits `pfl.capital` before losers debit it. |
| **Trader — Atomic Flip** | `[RefreshLeg... , Trade(mode=1, close), Trade(mode=0, open)]` | **~5,600 CU** *(1 leg)* | **≤ 793 B** | Atomic long↔short flip in 1 tx without a dedicated flip instruction. |
| **Trader — Withdraw Collateral** | `[RefreshLeg(m_i, trader)... , WithdrawCollateral]` *(0 `RefreshLeg`s if flat)* | **11,135 CU** *(8 legs)* | **793 B** / 1,232 B | Enforces fresh margins across all open legs before withdrawing (`flat_portfolio_unconditionally_withdrawable` skips refresh when flat). |
| **Trader — Position Hand-Off** | `[RefreshLeg(m_j, buyer)... , Trade(mode=2 or 3)]` | **9,944 / 10,651 CU** *(8 legs)* | **793 B** / 1,232 B | Transfers raw basis Long→Long or Short→Short with bit-for-bit invariant OI & ADL. |
| **Liquidation Keeper — Fallback (`mode=0`)** | `[RefreshLeg(other_m_i, victim)... , Liquidate(target_m, victim, mode=0)]` | **9,869 CU** *(8 legs)* | **690 B** / 1,232 B | Satisfies `checkAllLegsFreshLoop` (A1) so hedged winning legs are credited before judging `target_m` insolvent; omit `RefreshLeg(target_m)` so `Liquidate` itself captures `shortfall` for `I_m` draw. |
| **Liquidation Keeper — Takeover (`mode=1`)** | `[RefreshLeg(other_m_i, victim)... , RefreshLeg(m_j, taker)... , Liquidate(target_m, victim, mode=1)]` | **17,221 CU** *(16 legs)* | **876 B** / 1,232 B | Zero-ADL counterparty takeover (works even during active partial ADL). |
| **Stale-Market Escape (Zero Freeze Window)** | `[StartWindDown(stale_m), RefreshLeg(stale_m, trader), RefreshLeg(other_m_i, trader)... , Withdraw/Trade/Liquidate]` | **~3,500–12,000 CU** | **≤ 850 B** | Proven zero freeze window (`no_stale_market_freeze_liveness`): on the exact first slot `age > maxStaleness`, anyone can wind down and immediately refresh in 1 atomic tx. |
| **Wind-Down Drain** | `[ForceClosePair(m, pflL, pflS)...]` *(pack up to ~40 pairs/block)*, then `[ClearDeadLeg...]` → `ResolveMarket` | **2,717 CU** / pair | — | Strictly terminates to `OI = 0` (`forceClosePair_terminates_and_sound`, `proportionalRawReduction_preserves_oi_le_raw`). |

### Recommended Market Parameters Under `T`-Slot Adversarial-Leader Censorship

Assume adversarial validators can censor/reorder for `T - 1` consecutive slots and at least **1 honest leader** appears every `T` slots:

| Parameter | Required Bound | Guarantee |
|---|---|---|
| `Market.maxStaleness` | **`> T`** *(recommended `150–300` slots = 1–2 min)* | Blocks adversarial leaders from grief-triggering permissionless `StartWindDown` during `T - 1` censored slots (`censored_crank_no_premature_winddown`). |
| `OracleAdapter.maxFeedAge` | **`> T`** slots *(or `> 0.4·T` secs for Pyth)* | Ensures the honest leader on slot `T` can always crank a fresh feed (or carry `ewmaPrice` under `FLAG_HYBRID_AH`). |
| `K · maxMoveBps + liqFeeBps` | **`≤ mmBps`** *(e.g. `maxMoveBps=100`, `mmBps=500`, `liqFeeBps=100` → **`K = 4`**)* | Guarantees **0 bad debt** even if adversarial leaders include `UpdateOracle` on `K` consecutive slots while censoring `Liquidate` (`censored_oracle_k_steps_zero_bad_debt`). |
| `Matcher.spreadBps` | **`≥ maxMoveBps`** *(for passive on-chain LPs)* | Eliminates profitable 1-slot stale-mark front-running against passive LPs when a validator reorders `Trade` before `UpdateOracle`. |

---

## 7. Verification & Worst-Case Multi-Leg Benchmarks (LiteSVM / Agave 3.1.3)

See [`INVARIANTS.md`](INVARIANTS.md) for all **77 kernel-checked Lean 4 theorems** (`0 sorry`, `0` custom axioms). All **11 end-to-end suites** in [`svm-runner/src/main.rs`](svm-runner/src/main.rs) pass 100% with **zero vault mocks**:

### Worst-Case 8-Leg (`MAX_LEGS = 8`) & Double-8-Leg (16-Leg) CU and Wire-MTU Stress Benchmarks (Suite 11)

Every worst-case actor path (users, cranks, and liquidation keepers) executes in **one single legacy Solana transaction** (`≤ 876 B / 1,232 B` UDP MTU, zero LUT required) at **≤ 9.7% of Solana's 200,000 default CU budget** (~72× below Solana's 1.4M max tx CU limit):

| Role & Worst-Case Transaction | Compute Units | % of 200k Default CU | Legacy Wire Size | % of 1,232 B MTU |
|---|---:|---:|---:|---:|
| **User — 8-Leg Atomic Withdraw** `[8× RefreshLeg + WithdrawCollateral]` | **11,135 CU** | 5.6% | **793 B** | 64.4% |
| **User — Double-8-Leg Trade** `[16× RefreshLeg + Trade]` (both parties at 8 legs) | **19,361 CU** | 9.7% | **865 B** | 70.2% |
| **User — Position Hand-Off** `[7× RefreshLeg + Trade(mode=2 / mode=3)]` | **9,944 / 10,651 CU** | 5.0% / 5.3% | **793 B** | 64.4% |
| **User — Post-ADL Open** `[15× RefreshLeg + Trade(mode=0)]` | **19,169 CU** | 9.6% | **857 B** | 69.6% |
| **Liquidation Keeper — 8-Leg Fallback** `[7× RefreshLeg + Liquidate(mode=0)]` | **9,869 CU** | 4.9% | **690 B** | 56.0% |
| **Liquidation Keeper — Double-8-Leg Post-ADL Takeover** `[14× RefreshLeg + Liquidate(mode=1)]` | **17,221 CU** | 8.6% | **876 B** | 71.1% |
| **Crank — 8-Market Oracle Batch** `[8× UpdateOracle]` (1 tx) | **4,704 CU** | 2.4% | **702 B** | 57.0% |
| **Crank — Native Oracle Parsers (CPI)** (Pyth V2 / Chainlink OCR2 / Switchboard 128b / Ratio / EWMA live / AH / Push) | **2,442 / 2,400 / 3,344 / 2,699 / 2,716 / 2,593 / 366 CU** | 0.2%–1.7% | — | — |
| **Crank — 8-Market CPI & Wind-Down** (`OracleAdapter` max/8×, `ForceClosePair`, `ResolveMarket`) | **2,322** (18,555 total) / **2,717** / **396 CU** | 1.2%–1.4% | — | — |

### Full 11-Suite Verification Summary

1. **Suite 1 — On-Chain `InitDex` PDA Vault Creation (`5,303 CU`)**: Creates real SPL Token `DexVault` PDA on-chain despite 1-lamport pre-funding griefing; rejects real executable `noop.so` as `tokenProg`, fake `sysProg`, and wrong PDA bump.
2. **Suite 2 — Multi-Market Creation (`1,965 CU`)**: Rejects solvency-envelope violations; creates isolated `BTC`, `ETH`, `SCAM` markets.
3. **Suite 3 — Cross-Margin Capital Efficiency (`trade 2,627 CU`, `refresh 1,080 CU`, `oracle 590 CU`)**: Long $500 BTC + Short $500 ETH on $100 shared capital survives a 7.84% parallel drop via atomic `[RefreshLeg(ETH), RefreshLeg(BTC)]` with `$100` intact and zero liquidation; verifies stale-leg withdrawal rejection and atomic withdrawal (`4,043 CU`).
4. **Suite 4 — Anti-Reverse-Contagion + God-Mode `RUG/USD` 12× Shielding Immunity (`liq 3,015 CU`)**: Rejects bare `Liquidate(SCAM)` while `BTC` leg is stale; atomic `[RefreshLeg(BTC), Liquidate(SCAM)]` leaves Alice with exact `capital == BTC_MM`, `I_BTC`/`I_ETH` untouched; plus **Suite 4B** runs both Long-`RUG` and Short-`RUG` 12× god-mode oracle pump shielding attacks verifying `solLeg.reservedMm == $50`, `I_SOL` untouched, and Bob1/Bob2 paid **100.00% (`+$40`)** with zero haircut.
5. **Suite 5 — Runtime Security Regressions**: Rejects same-slot oracle spam, unclamped jumps, **real executable `noop.so` passed as `tokenProgram` across all 5 SPL CPI handlers (`Custom(120)`)**, wrong `mint` (`Custom(112)`), wrong `vaultPda` (`Custom(113)`), aliased trades, and live-OI insurance withdrawals.
6. **Suite 6 — Post-ADL Recovery, Full Lifecycle, Event Logs & Rent Reclaim (`clearDeadLeg 1,054 CU`, `closeAccount 248 CU`)**: Full ADL → `ClearDeadLeg` → `WindDown` → `ForceClosePair` → `Resolve` → `Tombstone` → `CloseAccount` reclaiming 100% rent across Portfolio, InsReceipt, and Market while verifying structured `sol_log_64_` events.
7. **Suite 7 — Core Composability & Donated-Insurance Tombstone**: Bounded `execPrice` spread transfer (rejects out-of-band), `oracleAuth`/`marketAdmin` rotation, `minMm` dust floor rejection, and permissionless insurance donation cleanly sweeping orphan donated insurance to `totalSurplus` on `ResolveMarket` + tombstoning.
8. **Suite 8 — 1,000-Step Stateful Fuzzer**: 474 valid randomized cross-margin transactions checking exact `C_tot + I_tot + R_tot + S_tot == V == SPL_balance` and all per-market/per-portfolio invariants after every tx — 0 violations.
9. **Suite 9 — External Multi-Program CPI Composition**:
   - `oracle_adapter.so` (`18,504 B`): verifies **Pyth V2 (`PriceUpdateV2`, 2,442 CU)** with `VerificationLevel::Full` & `feed_id` pinning, **Chainlink OCR2 (`Transmissions`, 2,400 CU)** with ring-buffer wraparound, **Switchboard On-Demand (`PullFeedAccountData`, 3,344 CU)** with 128-bit `PRECISION=18` scaling, **2-Leg Composite Ratio (`Pyth/Chainlink`, 2,699 CU)**, **EWMA Smoothing + Hybrid After-Hours (`live 2,716 CU / AH 2,593 CU / PushEwmaMark 366 CU`)** on a 2-leg `STOXX/SOL` ratio with stale-equity carry, bounded per-slot after-hours mark updates, and live market-open recovery, spoofed feed-owner rejection, and 4-slot smooth auto-clamped convergence (`$100 → $115`).
   - `matcher.so` (`8,552 B`, `open 4,355 CU`, `close 3,949 CU`, `withdrawLp 3,859 CU`): PDA-owned LP portfolio executes single-signer taker opens & closes with exact spread earned by LP and PDA-signed LP withdrawals.
   - **Suite 9C — Atomic Crank+LP Bundle & `K=4` Censored Liquidation (`6,715 CU, 552 B` / `3,319 CU`)**: Executes `[Crank(SOL), RefreshLeg(SOL, LP), Crank(ETH), RefreshLeg(ETH, LP)]` in one atomic tx, keeping a hedged spread immune to premature-liquidation reordering; verifies `K = 4` consecutive adverse `-1%` oracle slots without interleaved liquidations still liquidates with `shortfall == 0` and `I_SOL` untouched.
10. **Suite 10 — Core Hardening & Fair Partial Takeover (`4,473 CU`)**: Rejects unbounded `exitWindow`/`maxStaleness`, nonzero `warmupSlots`, and `Trade(mode=1)` spread draining below `totalMm`; verifies partial takeover with gradual deficit fee (`< maxFee`) and zero ADL on innocent counterparties.
11. **Suite 11 — Worst-Case 8-Leg CU/MTU Exhaustion + Anti-Selective-Liquidation + Post-ADL Recovery + Position Hand-Off**: Full 8-market, double-8-leg stress test verifying every role above, rejecting selective single-leg liquidation on an 8-leg hedged spread, verifying same-side Long→Long & Short→Short hand-off, post-ADL opens, post-ADL double-8-leg takeover, and full 8-market CPI/wind-down sweeps with zero invariant violations.

---

## 8. Build & Reproduce

```bash
# Run full Lean 4 kernel proof verification (77 theorems, 0 sorry, 0 custom axioms),
# compile all 3 sBPF .so binaries, and execute all 11 LiteSVM suites:
./scripts/build-and-test.sh
```
