# `percolator-lean` — Formally Verified Realizable Cross-Margin Perpetuals DEX on Solana

`percolator-lean` is a minimal, composable, formally verified Solana perpetuals DEX written in **Lean 4** and compiled directly to zero-heap Solana sBPF bytecode via [`lean-svm`](https://github.com/aeyakovenko/lean-svm).

It achieves **full cross-margin capital efficiency on healthy markets** (hedged spreads net 1:1 with zero warmup drag) while maintaining **machine-checked per-market risk isolation**: permissionlessly created or adversarial markets cannot drain other markets, untouched users, or other markets' insurance pools.

The repository ships a minimal core clearinghouse ([`percolator.so`](Percolator/Program.lean)) plus two tiny, formally verified composable external programs that integrate via CPI without bloating the core:
- **[`Percolator.Matcher`](Percolator/Matcher.lean)** (`8,752 B`) — permissionless passive-LP AMM / spread matcher enabling single-signer taker opens & closes against resting PDA-owned LP portfolios.
- **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** (`6,280 B`) — permissionless external price-feed bridge with confidence/staleness checks, smooth multi-slot auto-clamped convergence, and on-chain premium funding.

| Program | ELF `.so` Size | sBPF Insns | Stack | Heap | Formal Lean 4 Proofs (`0 sorry`) |
|---|---:|---:|---:|---:|---|
| **[`Percolator.Program`](Percolator/Program.lean)** (Core DEX) | **52,304 B** | 6,406 | 384 B | 0 B | 24 theorems (`Spec.lean` / `Proofs.lean`) |
| **[`Percolator.Matcher`](Percolator/Matcher.lean)** (LP AMM CPI) | **8,752 B** | 974 | 712 B | 0 B | 4 theorems (`quoteAsk/Bid` bounds & clamp) |
| **[`Percolator.OracleAdapter`](Percolator/OracleAdapter.lean)** (Feed + Funding CPI) | **6,280 B** | 661 | 368 B | 0 B | `crank_step_and_funding_within_clamp` |

---

## 1. Architecture & Composability

```
┌─────────────────────────────────┐     ┌──────────────────────────────────┐
│  Percolator.Matcher (8,752 B)   │     │ Percolator.OracleAdapter         │
│  • Passive LP AMM / Spreads     │     │ (6,280 B)                        │
│  • Single-Signer Taker Fill     │     │ • External Feed + Conf/Age Gate  │
│  • PDA-Owned LP Portfolio       │     │ • Auto-Clamped Step + Funding    │
└───────────────┬─────────────────┘     └───────────────┬──────────────────┘
                │ CPI (invoke_signed)                   │ CPI (invoke_signed)
                ▼  InitPortfolio / Trade / Withdraw     ▼  UpdateOracle
┌──────────────────────────────────────────────────────────────────────────┐
│                percolator-lean Core (52,304 B · 20 ops · 0 heap)         │
│  • Realizable Shared Cross-Margin      • On-Chain PDA Vault Creation     │
│  • Per-Market Isolated R_m / I_m / A_m • Exact C + I + R + S = V         │
│  • Bounded execPrice Spreads           • Unified CloseAccount Reclaim    │
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

### 2.2 Per-Leg Loss Containment (`cross_margin_isolation_envelope`)

Each `Portfolio` maintains `totalMm = ∑ active_leg.cachedMm` and `totalIm = ∑ active_leg.cachedIm`. When leg $j$ incurs a loss or liquidation fee, debits from shared `capital` are strictly capped at:

$$\text{capAvailableForLeg}(j) = \text{capital} - (\text{totalMm} - \text{leg}_j.\text{cachedMm})$$

This single rule proves both halves of `cross_margin_isolation_envelope`:
- **Anti-Reverse-Contagion:** Even an arbitrarily large crash on a toxic leg (`SCAM`) leaves $\text{capital}' \ge \text{otherMm}$, protecting unrelated healthy legs (`BTC`, `ETH`) and keeping their insurance pools bit-for-bit untouched.
- **Anti-Shielding:** Whenever a portfolio is healthy ($\text{capital} \ge \text{totalMm}$), $\text{capAvailableForLeg}(j) \ge \text{MM}_j \ge \text{stepLoss}_j + \text{liqFee}_j$ (under $\text{maxMoveBps} + \text{liqFeeBps} \le \text{mmBps}$), so fake legs can never shield capital from a healthy market's one-step loss + liquidation fee.

Each market may also set an immutable nonzero maintenance-margin floor `minMm` (`computeMarginWithFloor`), eliminating dust-position liquidation griefing while strictly strengthening solvency (`minMm_strengthens_solvency`).

### 2.3 Same-Slot Multi-Leg Freshness

- `RefreshLeg(dex, mkt, pfl)` is $O(1)$ and permissionless: verifies fresh oracle, settles `entryK → kSide`, realizes backed `posPnl`, updates `cachedMm`/`cachedIm`, and stamps `leg.lastRefreshSlot = curSlot`.
- `WithdrawCollateral` and risk-increasing `Trade(mode=0)` verify that every active open leg has `lastRefreshSlot == curSlot` (satisfied atomically in one transaction `[RefreshLeg(m1), ..., Withdraw/Trade]`). Flat portfolios withdraw unconditionally.
- Risk-reducing `Trade(mode=1)` and `Liquidate` remain strictly $O(1)$ without touching other markets.

### 2.4 Clamped Oracle Accounting, Derived Side ADL & Lifecycle

- **Per-slot rate limit & clamp:** `UpdateOracle` enforces `curSlot > lastOracleSlot` and $|\Delta P| + \text{fundE6} \le \lfloor P_{\text{old}} \cdot \text{maxMoveBps} / 10000 \rfloor$, with directional rounding guaranteeing credited gains $\le$ debited losses (`oracle_step_zero_sum`).
- **Derived side ADL & recovery:** $A_{\text{side}} = \max(1, \lfloor 10^9 \cdot \text{OI}_{\text{side}} / \text{rawBasis}_{\text{side}} \rfloor)$ (default $10^9$ when `rawBasis == 0` or `OI >= rawBasis`), ensuring effective exposure never exceeds OI (`deriveAdl_exposure_le_oi`). Post-ADL reductions deduct proportional raw basis, and `ClearDeadLeg` clears zero-OI legs and resets $A_{\text{side}} \to 10^9$.
- **Permissionless lifecycle:** `Active` → `WindDown` (by admin or permissionlessly when oracle is stale) → `ForceClosePair` (permissionless after `exitWindow`) → `ResolveMarket` (once `oi = rawBasis = activeLegs = 0`, snapshotting immutable `(resolvedNum, resolvedDen)`) → `ClaimResolved` (order-independent payout bounded in aggregate by `sum_resolved_payouts_le_realizedPool`) → `TombstoneMarket` (`insurance = totalPosPnl = 0`) → `CloseAccount` (zeroes magic and reclaims 100% rent).

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
| 11 | `Trade` | Bilateral open (`mode=0`) or proportional reduce (`mode=1`) with optional clamped `execPrice` spread |
| 12 | `Liquidate` | Permissionless $O(1)$ liquidation with per-leg loss containment & capped `I_m` draw |
| 13 | `ClearDeadLeg` | Permissionlessly clear zero-OI post-ADL leg & reset `adlSide → ADL_ONE` |
| 14 | `StartWindDown` | Admin or permissionless stale-oracle transition to `WindDown` |
| 15 | `ForceClosePair` | Permissionless post-`exitWindow` forced bilateral close |
| 16 | `ResolveMarket` | Snapshot immutable pro-rata payout ratio once `oi = rawBasis = activeLegs = 0` |
| 17 | `ClaimResolved` | Order-independent pro-rata claim from `R_m` into shared `pfl.capital` |
| 18 | `TombstoneMarket` | Permanently seal drained market (`I_m = 0 ∧ P^+_m = 0`) |
| 19 | `CloseAccount` | Unified rent reclaim for empty `Portfolio`, empty `InsReceipt`, or `Tombstoned` `Market` |

---

## 5. Verification & Benchmarks (LiteSVM / Agave 3.1.3)

See [`INVARIANTS.md`](INVARIANTS.md) for all **29 kernel-checked Lean 4 theorems** (`0 sorry`, `0` custom axioms). All 9 end-to-end suites in [`svm-runner/src/main.rs`](svm-runner/src/main.rs) pass 100% with **zero vault mocks**:

1. **Suite 1 — On-Chain `InitDex` PDA Vault Creation (`5,303 CU`)**: Creates real SPL Token `DexVault` PDA on-chain despite 1-lamport pre-funding griefing; rejects fake `tokenProg`, fake `sysProg`, and wrong PDA bump.
2. **Suite 2 — Multi-Market Creation (`1,959 CU`)**: Rejects solvency-envelope violations; creates isolated `BTC`, `ETH`, `SCAM` markets.
3. **Suite 3 — Cross-Margin Capital Efficiency (`trade 2,532 CU`, `refresh 1,161 CU`, `oracle 517 CU`)**: Long $500 BTC + Short $500 ETH on $100 shared capital survives a 7.84% parallel drop via atomic `[RefreshLeg(ETH), RefreshLeg(BTC)]` with `$100` intact and zero liquidation; verifies stale-leg withdrawal rejection and atomic withdrawal (`4,062 CU`).
4. **Suite 4 — Anti-Reverse-Contagion (`liquidate 1,799 CU`)**: 15-step malicious `SCAM` pump liquidates `SCAM` leaving Alice with exact `capital == BTC_MM`, `I_BTC`/`I_ETH` untouched, and attacker capped at `R_SCAM`.
5. **Suite 5 — Runtime Security Regressions**: Rejects same-slot oracle spam, unclamped jumps, fake `tokenProg`, aliased trades, and live-OI insurance withdrawals.
6. **Suite 6 — Post-ADL Recovery, Full Lifecycle & Rent Reclaim (`clearDeadLeg 1,032 CU`, `closeAccount 248 CU`)**: Full ADL → `ClearDeadLeg` → `WindDown` → `ForceClosePair` → `Resolve` → `Tombstone` → `CloseAccount` reclaiming 100% rent across Portfolio, InsReceipt, and Market.
7. **Suite 7 — Core Composability**: Bounded `execPrice` spread transfer (rejects out-of-band), `oracleAuth`/`marketAdmin` rotation, `minMm` dust floor rejection, and permissionless insurance donation.
8. **Suite 8 — 1,000-Step Stateful Fuzzer**: 458 valid randomized cross-margin transactions (including liquidations and `ClearDeadLeg`s) checking exact `C_tot + I_tot + R_tot + S_tot == V == SPL_balance` and all per-market/per-portfolio invariants after every tx — 0 violations.
9. **Suite 9 — External Multi-Program CPI Composition**:
   - `oracle_adapter.so` (`6,280 B`, `crank 2,111 CU`): rejects stale/wide-confidence feeds and smoothly converges `$100 → $115` over 4 permissionless slots via PDA-signed CPI into `UpdateOracle`.
   - `matcher.so` (`8,752 B`, `open 4,277 CU`, `close 3,804 CU`, `withdrawLp 3,809 CU`): PDA-owned LP portfolio executes single-signer taker opens & closes with exact spread earned by LP and PDA-signed LP withdrawals.

---

## 6. Build & Reproduce

```bash
# 1. Verify all 29 Lean 4 theorems (0 sorry, 0 custom axioms)
lake build

# 2. Compile core DEX + both composable external programs to sBPF (.so)
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.Program Percolator.Program.entrypoint -o build/percolator.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.Matcher Percolator.Matcher.entrypoint -o build/matcher.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.OracleAdapter Percolator.OracleAdapter.entrypoint -o build/oracle_adapter.so

# 3. Run all 9 LiteSVM verification, CPI composition, and 1,000-step fuzz suites
cargo run --manifest-path svm-runner/Cargo.toml --release -- \
  build/percolator.so build/matcher.so build/oracle_adapter.so
```
