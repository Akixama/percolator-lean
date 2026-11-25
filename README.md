# `percolator-lean` — Formally Verified Realizable Cross-Margin Perpetuals DEX on Solana

`percolator-lean` is a single-program, formally verified Solana perpetuals DEX written in **Lean 4** and compiled directly to zero-heap Solana sBPF bytecode via [`lean-svm`](https://github.com/aeyakovenko/lean-svm).

It achieves **full cross-margin capital efficiency on healthy markets** (hedged spreads net 1:1 with zero warmup drag) while maintaining **machine-checked per-market risk isolation**: permissionlessly created or adversarial markets cannot drain other markets, untouched users, or other markets' insurance pools.

| Property | Verified Result |
|---|---|
| **Compiled Binary (`percolator.so`)** | **46,072 bytes** (5,629 sBPF instructions, 384 B max stack, **0 B heap**) |
| **Formal Verification** | **22 Lean 4 kernel-checked theorems** (`0 sorry`, `0` custom axioms, `0` external Lean deps) |
| **LiteSVM Verification (Agave 3.1.3)** | **7/7 security, capital-efficiency, lifecycle & 1,000-step stateful fuzz suites PASS** |
| **Hot-Path Compute Units (LiteSVM)** | `UpdateOracle`: **517 CU** · `RefreshLeg`: **1,155 CU** · `Trade`: **2,399 CU** · `Liquidate`: **1,791 CU** |

---

## 1. Protocol Design

### 1.1 Core Problem: Capital Efficiency vs. Contagion Isolation

A perpetuals DEX with permissionless market creation faces a fundamental tension:

- **Fully isolated per-market vaults** prevent contagion, but force traders to split collateral across markets — a trader holding Long $500 BTC and Short $500 ETH on $100 equity gets liquidated on the losing leg during a parallel 8% drop even though net PnL is $0.
- **Naive shared cross-margin** nets PnL seamlessly, but lets a malicious or broken market (e.g., an adversarial oracle on `SCAM-PERP`) mint unbounded paper profits or drain a user's entire portfolio collateral, inducing bad debt into unrelated healthy markets (`BTC-PERP`, `ETH-PERP`) and their insurance pools.

`percolator-lean` resolves this tension with **Realizable Shared Cross-Margin**:

1. **One shared quote custody vault (`DexVault` PDA)** holds all quote collateral across the DEX, partitioned into four exact, disjoint accounting classes:
   $$C_{\text{tot}} + I_{\text{tot}} + R_{\text{tot}} + S_{\text{tot}} = V$$
   where:
   - $C_{\text{tot}} = \sum_{p} \text{capital}_p$ — users' shared senior cross-margin collateral across portfolios,
   - $I_{\text{tot}} = \sum_{m} I_m$ — per-market isolated insurance pools,
   - $R_{\text{tot}} = \sum_{m} R_m$ — per-market isolated realized loser pools (`realizedPool`),
   - $S_{\text{tot}} = \sum_{m} S_m$ — per-market rounding residue sinks,
   - $V$ — exact SPL Token balance held by `DexVault`.

2. **Per-market isolated profit backing ($R_m$) & insurance ($I_m$)**:
   - Positive PnL accrued on market $m$ (`posPnl`) is a claim **strictly against market $m$'s own `realizedPool` $R_m$** — never against $C_{\text{tot}}$, other markets' $R_{m'}$, or other markets' $I_{m'}$.
   - On healthy markets ($R_m \ge P^+_m$ with `warmupSlots == 0`), calling `RefreshLeg(m, p)` immediately credits `posPnl` **1:1 into shared `pfl.capital`** ($R_m \to C_{\text{tot}}$). A trader holding Long $500 BTC + Short $500 ETH on $100 shared capital executes `[RefreshLeg(ETH), RefreshLeg(BTC)]` atomically in a single Solana transaction: +$40 realized ETH profit flows directly into `capital`, offsetting -$40 BTC loss with **zero liquidation and zero haircut**.
   - On an insolvent or adversarial market ($R_m < P^+_m$), positive PnL payout is strictly bounded by the floor haircut ratio:
     $$\text{haircutPayout}(p, R_m, P^+_m) = \left\lfloor \frac{p \cdot \min(R_m, P^+_m)}{P^+_m} \right\rfloor \le \min(p, R_m)$$
     which is proven monotone non-decreasing for remaining claimants (`haircutPayout_monotone_ratio` — no first-mover drain).

3. **Per-leg loss containment (`cross_margin_isolation_envelope`)**:
   - Each `Portfolio` maintains `totalMm = ∑ active_leg.cachedMm` and `totalIm = ∑ active_leg.cachedIm`.
   - When leg $j$ suffers a loss (during `RefreshLeg`, `Trade`, `Liquidate`, or `ForceClosePair`), debits from shared `capital` are strictly capped at:
     $$\text{capAvailableForLeg}(j) = \text{capital} - (\text{totalMm} - \text{leg}_j.\text{cachedMm})$$
   - Liquidation fees on leg $j$ are likewise bounded strictly by remaining capital **above** $\text{otherMm} = \text{totalMm} - \text{leg}_j.\text{cachedMm}$.
   - This simultaneously proves two opposing safety properties (`cross_margin_isolation_envelope`):
     - **Anti-Reverse-Contagion:** Even if a toxic `SCAM` leg loses $10^{18}$, seizing `SCAM` losses and liquidation fees **always leaves $\text{capital}' \ge \text{otherMm}$**. Unrelated healthy legs (`BTC`, `ETH`) remain 100% solvent and their insurance pools are bit-for-bit untouched.
     - **Anti-Shielding:** Whenever a portfolio is healthy ($\text{capital} \ge \text{totalMm}$), we have $\text{capAvailableForLeg}(j) \ge \text{MM}_j \ge \text{stepLoss}_j + \text{liqFee}_j$ (via the clamped oracle solvency envelope $\text{maxMoveBps} + \text{liqFeeBps} \le \text{mmBps}$). Adding fake or toxic legs can **never** shield capital from covering a healthy market's one-step loss + liquidation fee.

### 1.2 Same-Slot Atomic Multi-Leg Freshness

To prevent stale-oracle withdrawal or leverage-expansion attacks on multi-leg portfolios while keeping `Liquidate` strictly $O(1)$:

- Every active leg stores `lastRefreshSlot`.
- `RefreshLeg(dex, mkt, pfl)` is $O(1)$ (touches 1 market), checks oracle freshness, settles `entryK → kSide`, realizes backed `posPnl` into `capital`, recomputes `cachedMm`/`cachedIm`, updates `totalMm`/`totalIm`, and stamps `lastRefreshSlot = curSlot`.
- `WithdrawCollateral` and risk-increasing `Trade(mode=0)` verify that **every active open leg** in the portfolio has `lastRefreshSlot == curSlot` (satisfied atomically in one Solana transaction `[RefreshLeg(m1), RefreshLeg(m2), Withdraw/Trade]`).
- Flat portfolios (0 open legs) satisfy freshness unconditionally and are always withdrawable.
- Risk-reducing `Trade(mode=1)` and `Liquidate` are strictly $O(1)$ and do not require other markets to be refreshed.

### 1.3 Clamped Oracle Accounting & Directional Rounding

Each market tracks cumulative per-unit PnL indices `kLong` and `kShort` (biased around $K_0 = 2^{62}$ to stay unsigned) updated on every `UpdateOracle`:

- **Per-slot rate limit:** `curSlot > lastOracleSlot` (at most one clamped step per Solana slot).
- **Per-step clamp:** $|\Delta P| + \text{fundE6} \le \lfloor P_{\text{old}} \cdot \text{maxMoveBps} / 10000 \rfloor$.
- **Solvency envelope** (enforced at `CreateMarket`):
  $$\text{maxMoveBps} + \text{liqFeeBps} \le \text{mmBps} < \text{imBps} \le 10000$$
- **Zero-sum directional rounding:** Winning side's $K$ delta is floored (`mulDivDown`), losing side's $K$ delta is ceiled (`mulDivUp`); positive leg PnL is floored, negative leg PnL is ceiled. Thus aggregate credited gains can never exceed aggregate debited losses (`oracle_step_zero_sum`).

### 1.4 Derived Side Auto-Deleveraging (ADL) & Post-ADL Recovery

When a liquidation exhausts a victim's available leg capital and capped insurance draw ($\le \lfloor I_m \cdot \text{maxInsDrawBps} / 10000 \rfloor$), open interest on both sides decreases symmetrically while the opposing side's `rawBasis` stays fixed. The opposing side's ADL index is derived deterministically rather than stored independently:

$$A_{\text{side}} = \begin{cases} 10^9 & \text{if } \text{rawBasis}_{\text{side}} = 0 \text{ or } \text{OI}_{\text{side}} \ge \text{rawBasis}_{\text{side}} \\ \max\!\left(1, \left\lfloor \frac{10^9 \cdot \text{OI}_{\text{side}}}{\text{rawBasis}_{\text{side}}} \right\rfloor\right) & \text{otherwise} \end{cases}$$

- **Effective quantity:** $q_{\text{eff}} = \lfloor \text{rawBasis}_{\text{leg}} \cdot A_{\text{side}} / 10^9 \rfloor$, guaranteeing aggregate effective exposure never exceeds OI (`deriveAdl_exposure_le_oi`).
- **Proportional post-ADL reduction:** Reducing $q$ units of OI on an ADL-haircutted side removes $\min(\text{rawLeg}, \max(1, \lceil q \cdot \text{rawSide} / \text{oiSide} \rceil))$ raw basis, preserving $\text{OI}_{\text{side}}' \le \text{rawBasis}_{\text{side}}'$.
- **Dead-leg cleanup (`ClearDeadLeg`):** Once a side's OI reaches $0$, any remaining ADL-zeroed legs on that side can be permissionlessly cleared, decrementing `rawBasisSide` and automatically resetting $A_{\text{side}} \to 10^9$ once `rawBasisSide == 0`.
- **Insurance lock:** `WithdrawInsurance` requires `oiLong == 0 ∧ oiShort == 0 ∧ rawBasisLong == 0 ∧ rawBasisShort == 0`, preventing insurance LPs from exiting while any live exposure or unresolved ADL basis exists.

### 1.5 Permissionless Market Lifecycle & Guaranteed Exit

```
Active ──(admin OR stale oracle)──▶ WindDown ──(oi=0 ∧ rawBasis=0 ∧ activeLegs=0)──▶ Resolved ──(I=0 ∧ P+=0)──▶ Tombstoned
```

1. **`Active`**: Normal trading, clamped oracle updates, refreshes, and $O(1)$ liquidations. Market admin may permanently burn their key (`BurnMarketAdmin`), making the market fully adminless.
2. **`WindDown`**: Triggered by market admin OR **permissionlessly by anyone** if `curSlot - lastOracleSlot > maxStaleness` (anti-oracle-liveness-DoS). New opens are halted; risk-reducing closes remain open.
3. **`ForceClosePair`**: After `exitWindow` slots ($\ge 10$) in `WindDown`, anyone can permissionlessly pair any open long leg against any open short leg to force-close OI strictly downward (`forceClosePair_terminates_and_sound`), preventing a recalcitrant counterparty from DoS-ing market resolution.
4. **`ResolveMarket` & `ClaimResolved`**: Once `oiLong = oiShort = rawBasisLong = rawBasisShort = activeLegs = 0`, anyone snapshots the immutable final ratio `resolvedNum = min(R_m, P^+_m)`, `resolvedDen = P^+_m`. Every flat winner then claims an **order-independent** payout $\lfloor \text{posPnl} \cdot \text{resolvedNum} / \text{resolvedDen} \rfloor$ directly into shared `pfl.capital`. By `sum_resolved_payouts_le_realizedPool`, the sum of all claimants' payouts can never exceed $R_m$.
5. **`TombstoneMarket`**: Once `insurance == 0 ∧ totalPosPnl == 0`, the market permanently enters `Tombstoned`, rejecting all further mutations.

---

## 2. Runtime Security Model

All on-chain account, PDA, and CPI boundaries are enforced directly in [`Percolator/Program.lean`](Percolator/Program.lean):

- **Pinned Canonical SPL Token Program ID:** Every token CPI checks all 32 bytes of `tokenProg` against `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA` (`PErr.invalidTokenProg`).
- **Cryptographic `DexVault` PDA + SPL Account Validation:** `InitDex` computes `sol_sha256(["dvlt", dex.key, bump, program_id, "ProgramDerivedAddress"])` on-chain, requires exact match with `vaultPda`, and validates that `vaultPda` is owned by `TOKEN_PROGRAM_ID`, has length $\ge 165$, matches `quoteMint`, is self-owned by `vaultPda`, has `amount == 0`, `state == Initialized`, `delegate == None`, and `close_authority == None`.
- **Anti-Aliasing & Ownership Checks:** Every account is validated for program ownership, minimum byte length, 4-byte account magic (`PDEX`, `MKTP`, `PFLO`, `INSR`), parent `dex`/`market`/`owner` key equality, and distinct long/short portfolio pubkeys in bilateral instructions.
- **Zero Admin Custody Access:** The protocol admin can only adjust `createFee` (`<= MAX_CREATE_FEE`) for future markets (`admin_updateCreateFee_zero_contagion`) and has zero authority over collateral, insurance, positions, or market parameters.

---

## 3. Account Layouts

| Account | Magic | Size | Key Fields |
|---|---|---:|---|
| **`Dex`** | `PDEX` | 200 B | `admin`, `quoteMint`, `vaultPda`, `vaultBump`, `decimals`, `feeVault`, `createFee`, `vaultBalance (V)`, `totalCapital (C_tot)`, `totalInsurance (I_tot)`, `totalResidual (R_tot)`, `totalSurplus (S_tot)` |
| **`Market`** | `MKTP` | 344 B | `status`, `marketId`, `dex`, `oracleAuth`, `marketAdmin`, `markPrice`, `lastOracleSlot`, `windDownSlot`, risk params (`imBps`, `mmBps`, `liqFeeBps`, `tradeFeeBps`, `maxMoveBps`, `maxInsDrawBps`, `maxOi`, `exitWindow`, `maxStaleness`, `warmupSlots`), `realizedPool (R_m)`, `insurance (I_m)`, `feeSurplus (S_m)`, `totalPosPnl (P^+_m)`, `oiLong/Short`, `rawBasisLong/Short`, `adlLong/Short`, `kLong/Short`, `resolvedNum/Den`, `activeLegs` |
| **`Portfolio`** | `PFLO` | 880 B | 112 B header (`legCount`, `portfolioId`, `episode`, `dex`, `owner`, `capital`, `totalMm`, `totalIm`) + **8 × 96 B `Leg` slots** (`active`, `side`, `marketId`, `market`, `rawBasis`, `entryK`, `posPnl`, `cachedMm`, `cachedIm`, `lastRefreshSlot`) |
| **`InsReceipt`** | `INSR` | 88 B | `marketId`, `owner`, `market`, `shares` |

---

## 4. Instruction Set (19 Unified Instructions)

Opcode dispatch is automatically compiled by `lean-svm` into a balanced $O(\log_2 19)$ binary search tree.

| Op | Instruction | Accounts | Purpose |
|---:|---|---|---|
| 0 | `InitDex` | `dex, admin, mint, vaultPda, feeVault, tokProg` | Initialize DEX with SHA-256 PDA & clean SPL vault verification |
| 1 | `UpdateCreateFee` | `dex, admin` | Update future market-creation fee (`<= MAX_CREATE_FEE`) |
| 2 | `CreateMarket` | `dex, mkt, mint, oracle, creator, creatorTok, feeVault, tokProg` | Permissionlessly create isolated market enforcing solvency envelope |
| 3 | `BurnMarketAdmin` | `mkt, admin` | Irreversibly burn market admin key |
| 4 | `UpdateOracle` | `mkt, oracle` | Rate-limited (`curSlot > lastOracleSlot`), clamped mark price + funding step |
| 5 | `InitPortfolio` | `dex, pfl, owner` | Initialize 8-leg shared cross-margin portfolio |
| 6 | `DepositCollateral` | `dex, pfl, owner, ownerTok, mint, vaultPda, tokProg` | Deposit quote SPL tokens into shared `pfl.capital` |
| 7 | `WithdrawCollateral` | `dex, pfl, owner, destTok, mint, vaultPda, tokProg` | Withdraw collateral (enforces same-slot leg freshness + `cap' >= totalIm`) |
| 8 | `DepositInsurance` | `dex, mkt, receipt, lp, lpTok, mint, vaultPda, tokProg` | Mint isolated LP shares for a specific market's insurance pool `I_m` |
| 9 | `WithdrawInsurance` | `dex, mkt, receipt, lp, destTok, mint, vaultPda, tokProg` | Burn LP shares for pro-rata `I_m` (requires `OI == 0 ∧ rawBasis == 0`) |
| 10 | `RefreshLeg` | `dex, mkt, pfl` | Permissionless $O(1)$ settle, backed `posPnl` realization, margin sync & slot stamp |
| 11 | `Trade` | `dex, mkt, pflL, ownerL, pflS, ownerS` | Bilateral `mode=0` open/increase (IM + freshness) or `mode=1` proportional reduce |
| 12 | `Liquidate` | `dex, mkt, pfl, liqTok, mint, vaultPda, tokProg` | Permissionless $O(1)$ liquidation with per-leg loss containment & capped `I_m` draw |
| 13 | `ClearDeadLeg` | `dex, mkt, pfl` | Permissionlessly clear zero-OI post-ADL leg & reset `adlSide → ADL_ONE` |
| 14 | `StartWindDown` | `mkt, caller` | Admin or permissionless stale-oracle transition to `WindDown` |
| 15 | `ForceClosePair` | `dex, mkt, pflL, pflS` | Permissionless post-`exitWindow` forced bilateral close |
| 16 | `ResolveMarket` | `mkt` | Snapshot immutable pro-rata payout ratio once `oi = rawBasis = activeLegs = 0` |
| 17 | `ClaimResolved` | `dex, mkt, pfl` | Order-independent pro-rata claim from `R_m` into shared `pfl.capital` |
| 18 | `TombstoneMarket` | `mkt` | Permanently seal drained market (`I_m = 0 ∧ P^+_m = 0`) |

---

## 5. Formal Verification & Testing

See [`INVARIANTS.md`](INVARIANTS.md) for the complete catalog of all **22 Lean 4 theorems** in [`Percolator/Proofs.lean`](Percolator/Proofs.lean) over the mathematical model in [`Percolator/Spec.lean`](Percolator/Spec.lean).

### LiteSVM Verification Suites ([`svm-runner/src/main.rs`](svm-runner/src/main.rs))

1. **Suite 1 — `InitDex` Hardening (`671 CU`)**: Rejects fake `tokenProg`, wrong PDA bump, non-zero vault balance, delegated vault, and `close_authority != None`; accepts valid SHA-256 PDA vault.
2. **Suite 2 — Multi-Market Creation (`1,950 CU`)**: Rejects solvency-envelope violations; creates isolated `BTC-PERP`, `ETH-PERP`, `SCAM-PERP` markets with independent insurance pools.
3. **Suite 3 — Cross-Margin Capital Efficiency (`trade 2,399 CU`, `refresh 1,155 CU`, `oracle 517 CU`)**: Alice deposits `$100`, opens Long `$500 BTC` + Short `$500 ETH` (`10×` gross leverage), survives a 2-slot `7.84%` parallel drop via atomic `[RefreshLeg(ETH), RefreshLeg(BTC)]` with `$100` intact and zero liquidation; verifies stale-leg `WithdrawCollateral` rejection and atomic `[RefreshLeg..., Withdraw]` success (`4,038 CU`).
4. **Suite 4 — Anti-Reverse-Contagion & Fake-PnL Containment (`liquidate 1,791 CU`)**: Malicious `SCAM-PERP` oracle pumps 15 consecutive steps against Alice's short while Alice holds Long `BTC-PERP`. `SCAM` liquidation leaves Alice with exact `capital == BTC_MM` (`23,040,000`), BTC leg remains healthy, `I_BTC`/`I_ETH` are bit-for-bit untouched, and attacker extraction is strictly capped at `R_SCAM`.
5. **Suite 5 — Runtime Security Regressions**: Rejects same-slot `UpdateOracle` spam, unclamped price jumps, fake `tokenProg` across all SPL CPIs, aliased `Trade`, and `WithdrawInsurance` while `OI > 0`.
6. **Suite 6 — Post-ADL Recovery & Full Lifecycle (`clearDeadLeg 1,028 CU`)**: Triggers full-side liquidation → ADL → `WithdrawInsurance` lock → `ClearDeadLeg` recovery (`adlShort → ADL_ONE`) → `BurnMarketAdmin` → stale-oracle `StartWindDown` → `ForceClosePair` → `ResolveMarket` → `ClaimResolved` → `WithdrawInsurance` → `TombstoneMarket`.
7. **Suite 7 — 1,000-Step Randomized Stateful Fuzzer**: Runs 1,000 randomized cross-margin operations (trend-biased clamped oracle updates, deposits, atomic refreshes/withdrawals, high-leverage trades, reductions, liquidations, and `ClearDeadLeg`s) across 3 markets and 5 portfolios, asserting exact `C_tot + I_tot + R_tot + S_tot == V == SPL_balance`, exact per-market/per-portfolio sums, balanced OI, ADL bounds, and margin cache coherence after **every single transaction** — 0 violations.

---

## 6. Build & Reproduce

```bash
# 1. Verify all 22 Lean 4 proofs (0 sorry, 0 custom axioms) and build program
lake build

# 2. Compile Percolator.Program.entrypoint directly to Solana sBPF ELF64 (.so)
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build \
  Percolator.Program Percolator.Program.entrypoint -o build/percolator.so

# 3. Run all 7 LiteSVM security, capital-efficiency, lifecycle, and 1,000-step fuzz suites
cargo run --manifest-path svm-runner/Cargo.toml --release -- build/percolator.so
```
