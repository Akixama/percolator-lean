# `percolator-lean` — Invariant Soundness Analysis & Security Charter

This document analyzes the security invariants of `percolator-lean`, a unified, zero-separation Lean 4 → Solana sBPF perpetual DEX designed for **permissionless multi-market / cross-chain synthetic positions with provable risk isolation**.

Unlike the legacy `percolator` + `percolator-prog` split (~1.9 MB of Rust across two crates, where engine proofs did not cover wrapper serialization, custody, or auth), `percolator-lean` is a **single unified Lean 4 codebase** compiled directly to minimal Solana sBPF bytecode via `lean-svm`. Every economic invariant below is **machine-checked in Lean 4's kernel (0 `sorry`, 0 custom axioms)** over the exact transition formulas compiled into the `.so`, and cross-verified end-to-end against real SPL Token accounts, PDAs, and CPIs on LiteSVM (`litesvm 0.11.0` / Agave `3.1.3`).

---

## 1. Why Naive Cross-Margin Is Unsound (Architectural Root-Cause Analysis)

A permissionless perps DEX faces a fundamental security trilemma if markets share a single vault or pool raw unrealized margin:

1. **Fake-PnL Extraction Attack**: An attacker creates a permissionless Market $B$ with a malicious oracle, opens a matched long/short against a sockpuppet, spikes the oracle $1000\times$, and uses their $+10^9$ paper PnL on $B$ to withdraw real USDC from Market $A$'s vault or back a position in Market $A$.
2. **Cross-Market Capital Seizure Attack**: Even *without* unrealized PnL credit, if Market $A$ and Market $B$ share the same unpartitioned collateral pool for a user, a malicious oracle spike on Market $B$ can drain $100\%$ of the user's shared collateral — turning that user's previously healthy Market $A$ position bankrupt and imposing bad debt on Market $A$'s insurance pool or Market $A$'s innocent counterparties who never touched Market $B$.
3. **First-Mover Haircut Drain & Flash-Oracle Dilution**: Inside a single market, if an attacker can credit and immediately withdraw unrealized positive PnL in the same slot before keepers liquidate an insolvent counterparty, the attacker steals residual backing owed to honest winners.
4. **Warmup-Reset Griefing DoS**: If a naive warmup resets its timer on every `+1` gain, a griefer can permissionlessly crank a victim's position every slot to permanently prevent PnL maturation.
5. **Self-Trade Insurance Theft**: If an oracle can gap past maintenance margin in a single slot and insurance unconditionally pays unlimited shortfalls, an attacker can self-trade leveraged longs/shorts around jumps to extract the insurance pool.
6. **Admin Rug vs. User Close-Griefing DoS**: If an admin can instantly close markets or seize insurance, the admin can rug users. Conversely, if a market cannot resolve until every user voluntarily closes, a single 1-unit dust position permanently DoSes market wind-down and insurance LPs.

### How `percolator-lean` Solves All Six by Construction

| Mechanism | Security Guarantee |
|---|---|
| **1. Per-Market Isolated SPL Vault PDA + Per-Market Insurance Pool** | Each Market $m$ owns its own SPL Vault PDA `[b"mvlt", market]` and its own `insurance_balance` $I_m$. Cross-market contagion is structurally and mathematically impossible. |
| **2. Cross-Market `Portfolio` Hub + Atomic `RebalanceMargin`** | Users deposit once into their personal `Portfolio` PDA and hold positions across arbitrary cross-chain oracle markets (BTC, ETH, SOL, etc.). `AllocateMargin` pledges explicit bounded collateral into Market $m$; `RebalanceMargin` atomically moves **realized, settled excess senior capital above IM** from `MarketVault_m1 → MarketVault_m2` in a single instruction. Paper PnL on a malicious Market $B$ can **never** enter Market $A$ unless backed by real SPL tokens inside `MarketVault_B`. |
| **3. Exact Solvency Conservation ($C_m + I_m + S_m \le V_m$)** | Every Market $m$ maintains Senior Capital $C_m = \sum c_i$, Insurance $I_m$, and Explicit Rounding/Fee Surplus $S_m$ strictly $\le V_m$. Residual backing is $R_m = V_m - C_m - I_m - S_m \ge 0$. Senior capital $c_i$ is NEVER haircut by another user's bad debt. |
| **4. 2-Bucket Epoch PnL Warmup (`pnl_curr`, `pnl_prev`, `pnl_mature`)** | Every new positive PnL atom enters `pnl_curr` at epoch $e = \lfloor \text{slot} / W \rfloor$ and only matures at epoch $e+2$: provably $\ge W$ slots anti-flash delay AND provably $\le 2W$ slots anti-griefing liveness regardless of permissionless cranks! |
| **5. Floor-Rounded Haircut $h_m = \min(1, R_m / P^+_m)$ + Monotonicity** | Converting mature `pnl_mature` to senior capital pays $\lfloor p \cdot \min(R_m, P^+_m) / P^+_m \rfloor$. Floor rounding provably NEVER reduces the haircut ratio for subsequent claimants and NEVER touches $C_m$ or $I_m$. |
| **6. Clamped Oracle Step + Solvency Envelope + Derived ADL $A_{\text{side}}$** | `UpdateOracle` clamps $|\Delta p| / p \le \text{max\_move\_bps}$ and funding $|\Delta f| \le \text{max\_funding}$, and `CreateMarket` enforces `max_move_bps + max_funding_bps + liq_fee_bps <= mm_bps < im_bps`. A healthy position CANNOT jump to negative equity in one step (0 bad debt, 0 insurance draw!). If stale keepers allow bankruptcy, insurance draw is capped by `min(shortfall, max_ins_draw, I_m)` with zero fee seniority, and uncovered OI is cleanly auto-deleveraged via exact derived $A_{\text{side}} = \lfloor \text{ADL\_ONE} \cdot \text{OI}_{\text{side}} / R_{\text{side}} \rfloor$. |
| **7. Zero-Rug Governance + Mandatory Exit Window + Permissionless Force-Close** | `protocol_admin` cannot touch ANY market or user funds. `market_admin` cannot withdraw user capital or insurance, can be burned to `0`, and `StartWindDown` (callable by admin OR permissionlessly on stale oracle!) freezes `mark_price` and grants `exit_window_slots` before permissionless `ForceClosePair` nets any remaining matched `(long, short)` pairs to zero OI, followed by immutable `ResolveMarket` snapshot and permanent `Tombstoned` close. |

---

## 2. Formal Invariant Catalog & Soundness Verification Matrix

Every invariant below is checked for **soundness** (does the theorem actually prevent the attack, or is it vacuously true / missing an edge case?) and linked directly to its Lean 4 kernel proof in `Percolator/Proofs.lean` and LiteSVM integration/adversarial test in `svm-runner/src/main.rs`.

### Group A — Conservation & Solvency (No Value Creation, No Vault Drain)

- **INV-1 (Vault Conservation)**: For every market $m$ and every reachable state,
  $$C_m + I_m + S_m \le V_m \quad \text{and} \quad R_m := V_m - C_m - I_m - S_m \ge 0.$$
  - *Soundness check*: Verified inductively across ALL state transitions (`Deposit/Allocate`, `Withdraw`, `Rebalance`, `Trade`, `UpdateOracle`, `Settle`, `RealizePnl`, `DepositInsurance`, `WithdrawInsurance`, `Liquidate`, `ForceClosePair`, `Resolve`, `ClaimResolved`). External token inflows/outflows match $\Delta V_m$ atom-for-atom via SPL `TransferChecked` CPI.
- **INV-2 (Exact Senior Capital & Positive PnL Aggregate Coherence)**:
  $$C_m = \sum_{u} \text{pos}(u,m).\text{capital}, \qquad P^+_m = \sum_{u} \text{pos}(u,m).\text{pnlTotal}.$$
  - *Soundness check*: Because every mutation updates both the individual position and the market aggregate by the exact same checked delta (and rejects aliased accounts `posA == posB`!), no user can ever hold senior capital exceeding $C_m$ or claim PnL exceeding $P^+_m$.
- **INV-3 (Protected Principal Seniority)**: No liquidation, ADL, oracle move, or bankruptcy of another user $u_2 \neq u_1$ can reduce $u_1$'s `capital` when $u_1$ is flat, nor can another user's bad debt ever debit $u_1$'s `capital`.
- **INV-4 (Haircut Conservation & Monotonicity — No First-Mover Drain)**:
  When a claimant realizes $p \le P^+_m$ from residual $R_m$ with $P^+_m > 0$,
  $$\text{payout} = \left\lfloor \frac{p \cdot \min(R_m, P^+_m)}{P^+_m} \right\rfloor$$
  satisfies:
  1. $\text{payout} \le p$ (never pays more than face claim),
  2. $\text{payout} \le R_m$ (never dips into $C_m$, $I_m$, or $S_m$),
  3. If $p < P^+_m$ and $R_m \le P^+_m$, then $(R_m - \text{payout}) \cdot P^+_m \ge R_m \cdot (P^+_m - p)$, i.e., **the haircut ratio for every remaining winner is non-decreasing**!
- **INV-5 (Zero Fee Seniority & Explicit Rounding Residue)**:
  - Liquidation fees and trading fees are strictly bounded by the payer's available equity (`fee <= available`); they are NEVER paid from $I_m$ or socialized.
  - Every directional rounding residue (`diff_up - diff_down >= 0`, floor payouts) increases $S_m$ or $R_m$ and never creates withdrawable claims or fake margin.

### Group B — Strict Risk Isolation (Cross-Market, User, and Insurance)

- **INV-6 (Absolute Market Isolation)**: Every instruction targeting Market $m_2$ (including `CreateMarket`, `UpdateOracle`, `Trade`, `Liquidate`, `RealizePnl`, `StartWindDown`, `ForceClosePair`, `ResolveMarket`) leaves every other Market $m_1 \neq m_2$ (`vault_balance`, `total_capital`, `insurance_balance`, `total_pos_pnl`, `oi`, all positions in $m_1$) **identically unchanged**.
- **INV-7 (Cross-Market Rebalance Soundness)**: `RebalanceMargin(m1 → m2, amount)` only moves **senior capital** strictly above $m_1$'s Initial Margin requirement AFTER settling $m_1$'s latest `K_side`, and transfers exact SPL tokens `MarketVault_m1 → MarketVault_m2`. Consequently:
  1. Market $m_1$ stays solvent (`C_{m1}' + I_{m1} + S_{m1} <= V_{m1}'`) and the user's $m_1$ position stays $\ge \text{IM}_{m1}$,
  2. Market $m_2$ receives real SPL backing (`ΔV_{m2} == ΔC_{m2} == amount`),
  3. Unbacked paper PnL from a malicious Market $m_1$ can **NEVER** cross into Market $m_2$.
- **INV-8 (Untouched User Isolation)**: No action by User $u_2$ in Market $m$ can reduce the `capital` of a flat User $u_1 \neq u_2$, nor reduce the `Portfolio` balance of any other user.
- **INV-9 (Insurance Pool Isolation & Anti-Theft)**:
  1. Insurance pool $I_{m_1}$ can ONLY be debited for shortfalls in Market $m_1$ (never $m_2$).
  2. Insurance withdrawal `WithdrawInsurance` is strictly pro-rata (`floor(shares * I_m / total_ins_shares)`), requires `oi_long == 0 && oi_short == 0`, and preserves $I_m \ge 0$ and $C_m + I_m + S_m \le V_m$.
  3. Under the clamped oracle solvency envelope (`max_price_move_bps + max_funding_bps + liq_fee_bps <= mm_bps`), a healthy position (`equity >= mm`) CANNOT go bankrupt (`equity' < 0`) in a single oracle update step — so `shortfall == 0` and **insurance draw is provably 0**!
  4. On multi-slot stale bankruptcy, insurance draw is strictly capped by `min(shortfall, cap, I_m)` and never touches $C_m$.

### Group C — Anti-Flash-Oracle & Anti-Griefing PnL Warmup

- **INV-10 (2-Bucket Epoch Warmup Soundness & Liveness)**:
  With `epoch(slot) = slot / W` ($W > 0$):
  1. **Safety (Anti-Flash-Oracle)**: Any positive PnL credited at `slot_0` enters `pnl_curr` at `e_0 = epoch(slot_0)` and is NOT present in `pnl_mature` at any `slot` with `epoch(slot) < e_0 + 2` (guaranteeing at least $W$ full slots of liquidation/crank visibility before realization).
  2. **Liveness (Anti-Griefing)**: Regardless of how many times a griefer calls `Settle` at any slots between `slot_0` and `slot_1`, once `epoch(slot_1) >= e_0 + 2` (at most $2W$ slots), any unburned portion of that gain is guaranteed to be in `pnl_mature`.
  3. **Exact Conservation**: `advanceWarmup` preserves `pnl_mature + pnl_prev + pnl_curr` identically (`ΔP^+_m == 0`).

### Group D — Bilateral OI Coherence, Derived ADL & Zero-Sum Settlement

- **INV-11 (Exact Bilateral OI Coherence)**: In `Active` and `WindDown` modes, `oi_long == oi_short <= max_oi`.
  - `Trade` adds/subtracts identical `q` on both legs (supporting open, increase, reduce, close).
  - Unilateral bankrupt liquidation (`Liquidate`) reduces `oi_short` (or `oi_long`) by `q` and simultaneously reduces the opposing side's `oi` by `q`, re-deriving $A_{\text{opp}}$.
- **INV-12 (Derived Side ADL Index Bound)**: Whenever `raw_basis_side > 0`,
  $$0 \le \text{oi}_{\text{side}} \le \text{raw\_basis}_{\text{side}}, \qquad A_{\text{side}} = \max\!\left(1, \left\lfloor \frac{\text{ADL\_ONE} \cdot \text{oi}_{\text{side}}}{\text{raw\_basis}_{\text{side}}} \right\rfloor\right) \le \text{ADL\_ONE},$$
  so exact side exposure $\text{raw\_basis}_{\text{side}} \cdot A_{\text{side}} / \text{ADL\_ONE} \le \text{oi}_{\text{side}}$ (never over-exposes!).
- **INV-13 (Risk-Reduction Availability)**: A user whose position is below Initial Margin is ALWAYS permitted to reduce or close their position (`|size'| < |size|`), preventing margin traps during volatility.

### Group E — Governance Containment, Anti-DoS Liveness & Replay/ABA Safety

- **INV-14 (Admin Non-Rug Containment)**:
  - `protocol_admin` cannot mutate any Market's state, vault, insurance, or user positions.
  - `market_admin` cannot debit user `capital`, cannot withdraw `insurance_balance` outside public LP share rules, cannot bypass `exit_window_slots`, and can be permanently burned (`market_admin = 0`).
- **INV-15 (No User-Caused Admin DoS & No Permanent User Lock — Two-Sided Liveness)**:
  - If oracle stalls (`slot >= last_oracle_slot + max_staleness_slots`), **anyone** can call `StartWindDown` (dead admin/oracle cannot lock funds).
  - Before `wind_down_slot + exit_window_slots`, `ForceClosePair` rejects (admin cannot instant-rug active traders).
  - After `wind_down_slot + exit_window_slots`, **anyone** can call `ForceClosePair(long, short)`, which strictly reduces `oi_long == oi_short` by `min(eff_L, eff_S) > 0` until `oi_long == oi_short == 0` (no griefer can hold open dust to block resolution!).
  - Once `oi_long == 0 && oi_short == 0`, anyone can call `ResolveMarket`, freezing `(resolved_num, resolved_den) = (min(R_m, P^+_m), P^+_m)` so every resolved claimant receives the **exact same order-independent payout rate**.
- **INV-16 (Incarnation, Aliasing, and Tombstone Integrity)**:
  - Every `Market` receives a strictly monotonic `market_id` from `ProtocolConfig.next_market_id` and closes into `status == Tombstoned (3)` (rejecting re-initialization forever).
  - Every `Position` binds `(market_id, position_id, episode)`.
  - Every 2-position / 2-market instruction rejects duplicate/aliased account pubkeys before mutation.

---

## 3. Explicit Trusted Computing Base (TCB) & Assumptions

To ensure complete honesty and zero hidden assumptions:
1. **Solana Runtime (SVM)**: Transaction atomicity & rollback on non-zero return code; ed25519 signature verification (`is_signer`); account ownership (`owner == program_id`); `Clock` sysvar monotonicity; SPL Token / Token-2022 custody and CPI semantics.
2. **Oracle Honesty Within a Single Market**: Within Market $m$, a malicious oracle can move `mark_price` up to `max_price_move_bps` per update — affecting ONLY participants who chose to trade Market $m$. **Market $m$'s oracle can NEVER affect any other market $m' \neq m$, any other insurance pool $I_{m'}$, or any user who did not allocate capital to Market $m$.**
3. **Keeper Liveness for Zero-Bad-Debt**: Under normal keeper liveness (liquidating within 1 oracle step of crossing `mm_bps`), bad debt is provably `0`. Even under total keeper failure (arbitrary multi-slot gaps), Vault Conservation (`INV-1`), Market Isolation (`INV-6`), Insurance Caps (`INV-9`), and ADL/Haircut Solvency (`INV-4`, `INV-12`) remain unconditionally proven!
4. **Compiler Faithfulness**: The formal proofs in `Percolator/Proofs.lean` verify the exact pure arithmetic & state-transition functions in `Percolator/Spec.lean`, and `Percolator/Program.lean` executes those exact formulas compiled directly to sBPF by `lean-svm` (verified end-to-end on real LiteSVM bytecode execution!).
