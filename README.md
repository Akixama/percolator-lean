# `percolator-lean` — Formally Verified, Risk-Isolated Multi-Market Perps DEX in Lean 4 → sBPF

`percolator-lean` is a **unified, formally verified Solana perpetuals DEX** written directly in Lean 4 and compiled straight to minimal Solana sBPF ELF64 (`.so`) bytecode via [`lean-svm`](https://github.com/aeyakovenko/lean-svm) — with **zero engine/program separation**, **zero heap allocation**, **zero external Lean dependencies**, and **zero `sorry` / zero custom axioms**.

## Design Goals & Risk Isolation

`percolator-lean` allows anyone to **permissionlessly create perpetual markets** (for any cross-chain asset price feed such as BTC, ETH, SOL, etc.) and hold **cross-market positions** from a unified `Portfolio` hub while **provably isolating all risk**:

- **A new/malicious market can NEVER hurt other markets, untouched users, or other insurance pools**: every market owns its own isolated SPL Vault PDA (`[b"mvlt", market]`), its own insurance pool $I_m$, its own open interest $(OI_L, OI_S)$, and its own derived ADL index $A_{\text{side}}$.
- **Cross-market positions with zero paper-PnL contagion**: users deposit once into their personal `Portfolio` PDA (`[b"pvlt", portfolio]`), allocate explicit bounded margin into chosen markets (`AllocateMargin`), and atomically rebalance excess settled senior capital across markets (`RebalanceMargin(m1 → m2)`). Unbacked paper PnL from a toxic market can never enter another market.
- **No insurance theft or first-mover drain**:
  - `CreateMarket` enforces the solvency envelope `maxMoveBps + liqFeeBps <= mmBps < imBps <= 10_000`.
  - `UpdateOracle` clamps 1-step price + funding deltas to `maxMoveBps`, proving **zero bad debt and zero insurance draw** on single-step liquidation of any healthy position (`oracle_clamp_zero_bad_debt`).
  - 2-bucket epoch PnL warmup (`pnl_curr → pnl_prev → pnl_mature`) proves BOTH **anti-flash-oracle delay ($\ge W$ slots)** AND **anti-griefing liveness ($\le 2W$ slots regardless of cranks)**.
  - Floor-rounded haircut `payout = floor(p * min(R_m, P^+_m) / P^+_m)` provably **never dips into senior capital or insurance** and **monotonically preserves/improves the ratio for remaining winners**.
- **No admin rug AND no user-caused admin DoS**:
  - `protocol_admin` can only set the bounded market creation fee — zero access to any market, vault, insurance pool, or user position.
  - `market_admin` cannot touch user capital or insurance, can be permanently burned (`BurnMarketAdmin`), and `StartWindDown` (callable by admin OR permissionlessly when the oracle goes stale) enforces a mandatory `exit_window_slots` grace period before permissionless `ForceClosePair` nets stubborn open pairs down to zero OI (`oiLong == oiShort == 0`), followed by an order-independent `ResolveMarket` snapshot and permanent `TombstoneMarket` (no ABA reuse).

See [`INVARIANTS.md`](INVARIANTS.md) for the complete invariant soundness analysis, adversarial threat matrix, and explicit Trusted Computing Base.

---

## Verified Metrics (`litesvm 0.11.0` / Agave `3.1.3`)

Compiled with **zero manual `@[noinline]` annotations** in [`Percolator/Program.lean`](Percolator/Program.lean) — all smart outlining, constant rematerialization, binary-search switch dispatch, load-CSE, and sBPF peephole folding are performed automatically by `lean-svm`.

| Metric | `percolator-lean` (`build/percolator.so`) |
|---|---|
| **ELF `.so` Object Size (all 22 instructions)** | **47,624 bytes** (46.5 KB) |
| **sBPF Instructions / Outlined Helpers** | **5,829 insns** / 47 auto-outlined helpers |
| **Max Stack Frame / Heap Allocation** | **384 bytes** / **0 bytes heap** |
| **Formal Proofs (`Percolator/Proofs.lean`)** | **20 kernel-checked theorems** (0 `sorry`, 0 custom axioms) |
| **LiteSVM Verification Suites** | **8/8 full lifecycle + adversarial attack suites PASS** |

### Measured LiteSVM Compute Units (Real SPL Token Accounts, PDAs & CPIs)

| Instruction | LiteSVM CUs | Notes |
|---|---:|---|
| `InitProtocol` | **216 CU** | Initializes monotonic `next_market_id` |
| `CreateMarket` (permissionless) | **1,972 CU** | Validates solvency envelope + SPL fee CPI |
| `DepositInsurance` | **1,742 CU** | Pro-rata isolated LP shares + SPL CPI |
| `AllocateMargin` (`Portfolio → Market`) | **1,974 CU** | PDA-signed SPL CPI |
| `RebalanceMargin` (`BTC → ETH`) | **2,400 CU** | Atomic cross-market excess-margin SPL CPI |
| `Trade` (bilateral matched Long/Short) | **1,331 CU** | Settle + exec-diff + fees→insurance + IM + OI |
| `UpdateOracle` (clamped + funding) | **512 CU** | Solvency-clamped mark + zero-sum `K_side` accrual |
| `SettleAndRealize` (warmup + haircut) | **593 / 642 CU** | 2-bucket epoch advance + floor haircut |
| `Liquidate` (permissionless + ADL) | **2,572 CU** | Includes SPL fee CPI + capped insurance + derived `A_side` |
| `ForceClosePair` (permissionless wind-down) | **795 CU** | Post-exit-window anti-DoS netting |
| `ResolveMarket` (permissionless snapshot) | **171 CU** | Freezes order-independent `(resolvedNum, resolvedDen)` |
| `ClaimResolved` (order-independent) | **2,070 CU** | Includes PDA-signed SPL payout CPI |
| `WithdrawInsurance` (post-zero-OI) | **1,863 CU** | Includes PDA-signed SPL payout CPI |

---

## Project Layout

- [`INVARIANTS.md`](INVARIANTS.md) — Complete soundness analysis of all 16 security invariant groups & TCB
- [`Percolator/Layout.lean`](Percolator/Layout.lean) — Shared scales, error codes, and exact zero-copy byte layouts (`ProtocolConfig`, `Market`, `Position`, `Portfolio`, `InsReceipt`)
- [`Percolator/Spec.lean`](Percolator/Spec.lean) — Pure mathematical multi-market `DexState` transition model
- [`Percolator/Proofs.lean`](Percolator/Proofs.lean) — 20 Lean 4 kernel-checked soundness, conservation, isolation, anti-flash, anti-griefing, anti-insurance-theft, and termination proofs
- [`Percolator/Program.lean`](Percolator/Program.lean) — Unified 22-instruction Lean 4 Solana program (~510 lines, zero engine/program split, zero manual `@[noinline]`)
- [`svm-runner/src/main.rs`](svm-runner/src/main.rs) — End-to-end LiteSVM lifecycle + adversarial attack test harness
- [`scripts/build-and-test.sh`](scripts/build-and-test.sh) — One-command proof check, sBPF compilation, and LiteSVM verification

---

## Quick Start

Requires [`lean-svm`](https://github.com/aeyakovenko/lean-svm) checked out alongside this repository (`../lean-svm`).

```bash
# 1. Verify all 20 Lean 4 formal proofs (0 sorry, 0 custom axioms)
lake build

# 2. Compile Percolator.Program directly to Solana sBPF (.so)
mkdir -p build
lake exe lean-svm build Percolator.Program Percolator.Program.entrypoint -o build/percolator.so

# 3. Run full LiteSVM lifecycle + adversarial security test suite
cargo run --manifest-path svm-runner/Cargo.toml --release -- build/percolator.so
```
