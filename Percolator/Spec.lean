/-
  Percolator.Spec
  Pure mathematical state-transition model for `percolator-lean` over exact natural
  arithmetic (`Nat`). Every economic formula in `Percolator.Program` implements these
  exact transitions using checked `UInt64` + 128-bit `mulDiv64`/`mulDiv64Ceil`.
-/

namespace Percolator.Spec

/-! ### Pure Mathematical Constants (matching `Percolator.Layout`) -/

def posScaleNat   : Nat := 1_000_000
def adlOneNat     : Nat := 1_000_000_000
def bpsDenNat     : Nat := 10_000
def minExitWinNat : Nat := 10

/-! ### Core Exact Arithmetic Primitives -/

/-- Exact floor division `⌊a * b / d⌋` (0 if `d = 0`). -/
def mulDivDown (a b d : Nat) : Nat :=
  if d = 0 then 0 else (a * b) / d

/-- Exact ceiling division `⌈a * b / d⌉` (0 if `d = 0`). -/
def mulDivUp (a b d : Nat) : Nat :=
  if d = 0 then 0 else (a * b + d - 1) / d

/-- Junior PnL realization payout: `⌊p * min(R, P) / P⌋`.
    Never exceeds `p`, never exceeds `R`, and monotonically preserves/improves `R / P`. -/
def haircutPayout (p residual posPnlTot : Nat) : Nat :=
  if posPnlTot = 0 then 0
  else (p * min residual posPnlTot) / posPnlTot

/-- Derived side ADL index: `max(1, ⌊ADL_ONE * oi / rawBasis⌋)` when `rawBasis > 0`,
    and `ADL_ONE` when `rawBasis = 0` or `oi = rawBasis`. -/
def deriveAdl (oi rawBasis : Nat) : Nat :=
  if rawBasis = 0 then adlOneNat
  else if oi >= rawBasis then adlOneNat
  else max 1 ((adlOneNat * oi) / rawBasis)

/-- Effective position quantity from `rawBasis` and `adlSide` (rounded down for exposure). -/
def effectiveQty (rawBasis adlSide : Nat) : Nat :=
  (rawBasis * adlSide) / adlOneNat

/-- Conservative margin notional `⌈qty * price / POS_SCALE⌉`. -/
def marginNotional (qty price : Nat) : Nat :=
  mulDivUp qty price posScaleNat

/-- Conservative margin requirement `⌈notional * bps / 10_000⌉`. -/
def marginReq (notional bps : Nat) : Nat :=
  mulDivUp notional bps bpsDenNat

/-- Oracle 1-step clamp condition: `|newP - oldP| * 10_000 ≤ oldP * maxMoveBps`. -/
def oracleClampOk (oldP newP maxMoveBps : Nat) : Prop :=
  let diff := if newP ≥ oldP then newP - oldP else oldP - newP
  diff * bpsDenNat ≤ oldP * maxMoveBps

/-! ### State Types -/

inductive MarketStatus where
  | active
  | windDown
  | resolved
  | tombstoned
  deriving DecidableEq, Repr

inductive Side where
  | flat
  | long
  | short
  deriving DecidableEq, Repr

structure MarketState where
  marketId      : Nat
  status        : MarketStatus
  marketAdmin   : Nat          -- 0 = burned (adminless)
  markPrice     : Nat
  lastOracleSlot: Nat
  windDownSlot  : Nat
  exitWindow    : Nat
  maxStaleness  : Nat
  warmupSlots   : Nat
  imBps         : Nat
  mmBps         : Nat
  liqFeeBps     : Nat
  tradeFeeBps   : Nat
  maxMoveBps    : Nat
  maxInsDrawBps : Nat
  maxOi         : Nat
  vault         : Nat          -- V_m
  totalCapital  : Nat          -- C_m
  insurance     : Nat          -- I_m
  feeSurplus    : Nat          -- S_m
  totalPosPnl   : Nat          -- P^+_m
  totalInsShares: Nat
  oiLong        : Nat
  oiShort       : Nat
  rawBasisLong  : Nat
  rawBasisShort : Nat
  adlLong       : Nat
  adlShort      : Nat
  resolvedNum   : Nat
  resolvedDen   : Nat
  activePos     : Nat
  deriving DecidableEq, Repr

structure PosState where
  marketId  : Nat
  owner     : Nat
  side      : Side
  claimed   : Bool
  capital   : Nat
  rawBasis  : Nat
  pnlMature : Nat
  pnlPrev   : Nat
  pnlCurr   : Nat
  pnlEpoch  : Nat
  episode   : Nat
  deriving DecidableEq, Repr

def PosState.pnlTotal (p : PosState) : Nat :=
  p.pnlMature + p.pnlPrev + p.pnlCurr

def MarketState.residual (m : MarketState) : Nat :=
  m.vault - (m.totalCapital + m.insurance + m.feeSurplus)

/-- Whole-DEX multi-market state (arbitrary number of isolated markets, positions,
    cross-market portfolios, and per-market insurance LP share receipts). -/
structure DexState where
  protocolAdmin : Nat
  nextMarketId  : Nat
  createFee     : Nat
  markets       : Nat → Option MarketState
  positions     : Nat → Nat → Option PosState   -- marketId → owner → PosState
  portfolios    : Nat → Nat                     -- owner → unallocated portfolio balance
  insShares     : Nat → Nat → Nat               -- marketId → lpOwner → shares

/-! ### 2-Bucket Epoch PnL Warmup State Machine -/

/-- Advance a position's 2-bucket epoch warmup to epoch `e = slot / warmupSlots`.
    Preserves `pnlTotal` identically; guarantees ≥ 1 full epoch anti-flash delay AND
    ≤ 2 epochs anti-griefing liveness regardless of permissionless cranks. -/
def advanceWarmup (p : PosState) (e : Nat) : PosState :=
  if e ≥ p.pnlEpoch + 2 then
    { p with
      pnlMature := p.pnlMature + p.pnlPrev + p.pnlCurr
      pnlPrev   := 0
      pnlCurr   := 0
      pnlEpoch  := e }
  else if e = p.pnlEpoch + 1 then
    { p with
      pnlMature := p.pnlMature + p.pnlPrev
      pnlPrev   := p.pnlCurr
      pnlCurr   := 0
      pnlEpoch  := e }
  else
    p

/-- Credit a positive mark/funding gain `gain` at epoch `e` into `pnlCurr`. -/
def applyGain (p : PosState) (gain e : Nat) : PosState :=
  let p1 := advanceWarmup p e
  { p1 with pnlCurr := p1.pnlCurr + gain }

/-- Apply a loss `loss`: burn `pnlCurr` → `pnlPrev` → `pnlMature` → `capital`.
    Returns `(newPos, pnlBurned, capDebited, shortfall)`. -/
def applyLoss (p : PosState) (loss : Nat) : PosState × Nat × Nat × Nat :=
  let bCurr := min loss p.pnlCurr
  let rem1  := loss - bCurr
  let bPrev := min rem1 p.pnlPrev
  let rem2  := rem1 - bPrev
  let bMat  := min rem2 p.pnlMature
  let rem3  := rem2 - bMat
  let pnlBurned := bCurr + bPrev + bMat
  let capDeb := min rem3 p.capital
  let shortfall := rem3 - capDeb
  let p' : PosState := { p with
    pnlCurr   := p.pnlCurr - bCurr
    pnlPrev   := p.pnlPrev - bPrev
    pnlMature := p.pnlMature - bMat
    capital   := p.capital - capDeb }
  (p', pnlBurned, capDeb, shortfall)

/-! ### Core Per-Market Invariant Predicates -/

def MarketState.vaultConserved (m : MarketState) : Prop :=
  m.totalCapital + m.insurance + m.feeSurplus ≤ m.vault

def MarketState.oiBalanced (m : MarketState) : Prop :=
  (m.status = .active ∨ m.status = .windDown) →
    m.oiLong = m.oiShort ∧ m.oiLong ≤ m.maxOi

def MarketState.adlValid (m : MarketState) : Prop :=
  m.oiLong ≤ m.rawBasisLong ∧
  m.oiShort ≤ m.rawBasisShort ∧
  m.adlLong ≤ adlOneNat ∧
  m.adlShort ≤ adlOneNat

def MarketState.solvencyEnvelope (m : MarketState) : Prop :=
  m.maxMoveBps + m.liqFeeBps ≤ m.mmBps ∧
  m.mmBps < m.imBps ∧
  m.imBps ≤ bpsDenNat ∧
  m.warmupSlots ≥ 1 ∧
  m.exitWindow ≥ minExitWinNat

def MarketState.wf (m : MarketState) : Prop :=
  m.vaultConserved ∧ m.oiBalanced ∧ m.adlValid ∧ m.solvencyEnvelope

/-! ### Pure State Transitions (Exact Specification of Every Instruction) -/

def updateFn {α β : Type} [DecidableEq α] (f : α → β) (k : α) (v : β) : α → β :=
  fun x => if x = k then v else f x

/-- Update protocol creation fee (only touches `createFee`; zero access to any market/user). -/
def stepUpdateCreateFee (st : DexState) (signer newFee : Nat) : Option DexState :=
  if signer = st.protocolAdmin then
    some { st with createFee := newFee }
  else
    none

/-- Burn market admin irreversibly to `0` (adminless immutable market). -/
def stepBurnMarketAdmin (st : DexState) (mid signer : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status ≠ .tombstoned ∧ m.marketAdmin ≠ 0 ∧ signer = m.marketAdmin then
    let m' := { m with marketAdmin := 0 }
    some { st with markets := updateFn st.markets mid (some m') }
  else
    none

/-- Deposit/Allocate margin from user's cross-market `Portfolio` into Market `mid`. -/
def stepAllocateMargin (st : DexState) (mid owner amount : Nat) : Option DexState := do
  let m ← st.markets mid
  let p ← st.positions mid owner
  if m.status = .active ∧ amount > 0 ∧ st.portfolios owner ≥ amount then
    let m' := { m with
      vault        := m.vault + amount
      totalCapital := m.totalCapital + amount }
    let p' := { p with capital := p.capital + amount }
    some { st with
      markets    := updateFn st.markets mid (some m')
      positions  := updateFn st.positions mid (updateFn (st.positions mid) owner (some p'))
      portfolios := updateFn st.portfolios owner (st.portfolios owner - amount) }
  else
    none

/-- Withdraw excess senior capital from Market `mid` back to user's `Portfolio`. -/
def stepWithdrawMargin (st : DexState) (mid owner amount : Nat) : Option DexState := do
  let m ← st.markets mid
  let p ← st.positions mid owner
  let eff := match p.side with
    | .flat  => 0
    | .long  => effectiveQty p.rawBasis m.adlLong
    | .short => effectiveQty p.rawBasis m.adlShort
  let im := marginReq (marginNotional eff m.markPrice) m.imBps
  if (m.status = .active ∨ m.status = .windDown) ∧
     amount > 0 ∧ p.capital ≥ amount ∧ m.totalCapital ≥ amount ∧
     m.vault ≥ amount ∧ (p.capital - amount ≥ im) then
    let m' := { m with
      vault        := m.vault - amount
      totalCapital := m.totalCapital - amount }
    let p' := { p with capital := p.capital - amount }
    some { st with
      markets    := updateFn st.markets mid (some m')
      positions  := updateFn st.positions mid (updateFn (st.positions mid) owner (some p'))
      portfolios := updateFn st.portfolios owner (st.portfolios owner + amount) }
  else
    none

/-- Cross-market atomic `RebalanceMargin(m1 → m2, amount)`:
    Moves ONLY settled excess senior capital above `IM` from Market `m1` directly
    to Market `m2` (real SPL tokens `MarketVault_m1 → MarketVault_m2`).
    Rejects `m1 = m2` (aliasing). Never moves unbacked paper PnL! -/
def stepRebalanceMargin (st : DexState) (m1Id m2Id owner amount : Nat) : Option DexState := do
  if m1Id = m2Id then none
  let m1 ← st.markets m1Id
  let m2 ← st.markets m2Id
  let p1 ← st.positions m1Id owner
  let p2 ← st.positions m2Id owner
  let eff1 := match p1.side with
    | .flat  => 0
    | .long  => effectiveQty p1.rawBasis m1.adlLong
    | .short => effectiveQty p1.rawBasis m1.adlShort
  let im1 := marginReq (marginNotional eff1 m1.markPrice) m1.imBps
  if (m1.status = .active ∨ m1.status = .windDown) ∧ m2.status = .active ∧
     amount > 0 ∧ p1.capital ≥ amount ∧ m1.totalCapital ≥ amount ∧
     m1.vault ≥ amount ∧ (p1.capital - amount ≥ im1) then
    let m1' := { m1 with vault := m1.vault - amount, totalCapital := m1.totalCapital - amount }
    let m2' := { m2 with vault := m2.vault + amount, totalCapital := m2.totalCapital + amount }
    let p1' := { p1 with capital := p1.capital - amount }
    let p2' := { p2 with capital := p2.capital + amount }
    let mkts1 := updateFn st.markets m1Id (some m1')
    let mkts2 := updateFn mkts1 m2Id (some m2')
    let pos1 := updateFn st.positions m1Id (updateFn (st.positions m1Id) owner (some p1'))
    let pos2 := updateFn pos1 m2Id (updateFn (pos1 m2Id) owner (some p2'))
    some { st with markets := mkts2, positions := pos2 }
  else
    none

/-- Realize mature positive PnL in Market `mid` into senior capital at `h_m = min(1, R_m / P^+_m)`. -/
def stepRealizePnl (st : DexState) (mid owner epoch : Nat) : Option DexState := do
  let m ← st.markets mid
  let p0 ← st.positions mid owner
  let p := advanceWarmup p0 epoch
  if (m.status = .active ∨ m.status = .windDown) ∧
     p.pnlMature > 0 ∧ m.totalPosPnl ≥ p.pnlMature then
    let pay := haircutPayout p.pnlMature m.residual m.totalPosPnl
    let m' := { m with
      totalCapital := m.totalCapital + pay
      totalPosPnl  := m.totalPosPnl - p.pnlMature }
    let p' := { p with
      capital   := p.capital + pay
      pnlMature := 0 }
    some { st with
      markets   := updateFn st.markets mid (some m')
      positions := updateFn st.positions mid (updateFn (st.positions mid) owner (some p')) }
  else
    none

/-- Deposit into Market `mid`'s isolated insurance pool (pro-rata LP shares). -/
def stepDepositInsurance (st : DexState) (mid lp amount : Nat) : Option DexState := do
  let m ← st.markets mid
  if (m.status = .active ∨ m.status = .windDown) ∧ amount > 0 then
    let minted :=
      if m.totalInsShares = 0 ∨ m.insurance = 0 then amount
      else (amount * m.totalInsShares) / m.insurance
    if minted = 0 then none
    let m' := { m with
      vault          := m.vault + amount
      insurance      := m.insurance + amount
      totalInsShares := m.totalInsShares + minted }
    let prevShares := st.insShares mid lp
    some { st with
      markets   := updateFn st.markets mid (some m')
      insShares := updateFn st.insShares mid (updateFn (st.insShares mid) lp (prevShares + minted)) }
  else
    none

/-- Withdraw from Market `mid`'s isolated insurance pool (ONLY when `oiLong = 0 ∧ oiShort = 0`,
    strictly pro-rata `⌊shares * I_m / totalInsShares⌋`, never touching `C_m`). -/
def stepWithdrawInsurance (st : DexState) (mid lp burnShares : Nat) : Option DexState := do
  let m ← st.markets mid
  let curShares := st.insShares mid lp
  if m.status ≠ .tombstoned ∧ m.oiLong = 0 ∧ m.oiShort = 0 ∧
     burnShares > 0 ∧ curShares ≥ burnShares ∧ m.totalInsShares ≥ burnShares then
    let pay := (burnShares * m.insurance) / m.totalInsShares
    let m' := { m with
      vault          := m.vault - pay
      insurance      := m.insurance - pay
      totalInsShares := m.totalInsShares - burnShares }
    some { st with
      markets   := updateFn st.markets mid (some m')
      insShares := updateFn st.insShares mid (updateFn (st.insShares mid) lp (curShares - burnShares)) }
  else
    none

/-- Bilateral matched open/increase trade on Market `mid` between distinct `longOwner ≠ shortOwner`:
    Opens/grows `qty > 0` on both sides, enforces `oiLong = oiShort ≤ maxOi`, enforces `adl = ADL_ONE`,
    charges trading fee to Market `mid`'s own insurance pool (zero fee seniority!). -/
def stepTradeOpen (st : DexState) (mid longOwner shortOwner qty : Nat) : Option DexState := do
  if longOwner = shortOwner then none
  let m ← st.markets mid
  let pL ← st.positions mid longOwner
  let pS ← st.positions mid shortOwner
  let fee := marginReq (marginNotional qty m.markPrice) m.tradeFeeBps
  let newBasisL := pL.rawBasis + qty
  let newBasisS := pS.rawBasis + qty
  let imL := marginReq (marginNotional newBasisL m.markPrice) m.imBps
  let imS := marginReq (marginNotional newBasisS m.markPrice) m.imBps
  if m.status = .active ∧ qty > 0 ∧
     m.adlLong = adlOneNat ∧ m.adlShort = adlOneNat ∧
     (pL.side = .flat ∨ pL.side = .long) ∧ (pS.side = .flat ∨ pS.side = .short) ∧
     m.oiLong + qty ≤ m.maxOi ∧ m.oiShort + qty ≤ m.maxOi ∧
     pL.capital ≥ fee + imL ∧ pS.capital ≥ fee + imS ∧
     m.totalCapital ≥ 2 * fee then
    let m' := { m with
      totalCapital  := m.totalCapital - 2 * fee
      insurance     := m.insurance + 2 * fee
      oiLong        := m.oiLong + qty
      oiShort       := m.oiShort + qty
      rawBasisLong  := m.rawBasisLong + qty
      rawBasisShort := m.rawBasisShort + qty }
    let pL' := { pL with side := .long,  rawBasis := newBasisL, capital := pL.capital - fee, episode := pL.episode + 1 }
    let pS' := { pS with side := .short, rawBasis := newBasisS, capital := pS.capital - fee, episode := pS.episode + 1 }
    let mPos1 := updateFn (st.positions mid) longOwner (some pL')
    let mPos2 := updateFn mPos1 shortOwner (some pS')
    some { st with
      markets   := updateFn st.markets mid (some m')
      positions := updateFn st.positions mid mPos2 }
  else
    none

/-- Permissionless unilateral liquidation of an under-maintenance position on Market `mid`:
    Applies `loss`, pays liquidation fee ONLY from remaining `capital` (zero fee seniority!),
    draws capped insurance `insDraw ≤ min(shortfall, cap, I_m)` into residual,
    and reduces both sides' OI by `eff` with exact derived ADL on the opposing side! -/
def stepLiquidate (st : DexState) (mid victim liqFeeCap loss : Nat) : Option DexState := do
  let m ← st.markets mid
  let p ← st.positions mid victim
  if m.status = .active ∧ p.side ≠ .flat ∧ p.rawBasis > 0 then
    let (p1, pnlBurned, capDeb, shortfall) := applyLoss p loss
    let liqFee := min liqFeeCap p1.capital
    let p2 := { p1 with capital := p1.capital - liqFee, side := .flat, rawBasis := 0, episode := p1.episode + 1 }
    let maxInsDraw := (m.insurance * m.maxInsDrawBps) / bpsDenNat
    let insDraw := min shortfall (min maxInsDraw m.insurance)
    -- Effective OI closed (symmetric reduction on both sides + derived ADL on opposite side)
    let (eff, newOiL, newOiS, newRawL, newRawS, newAdlL, newAdlS) :=
      match p.side with
      | .long =>
          let e := min (effectiveQty p.rawBasis m.adlLong) (min m.oiLong m.oiShort)
          let oiL' := m.oiLong - e
          let oiS' := m.oiShort - e
          let rL'  := m.rawBasisLong - p.rawBasis
          let rS'  := m.rawBasisShort
          (e, oiL', oiS', rL', rS', deriveAdl oiL' rL', deriveAdl oiS' rS')
      | .short =>
          let e := min (effectiveQty p.rawBasis m.adlShort) (min m.oiLong m.oiShort)
          let oiL' := m.oiLong - e
          let oiS' := m.oiShort - e
          let rL'  := m.rawBasisLong
          let rS'  := m.rawBasisShort - p.rawBasis
          (e, oiL', oiS', rL', rS', deriveAdl oiL' rL', deriveAdl oiS' rS')
      | .flat => (0, m.oiLong, m.oiShort, m.rawBasisLong, m.rawBasisShort, m.adlLong, m.adlShort)
    if m.totalCapital ≥ capDeb + liqFee ∧ m.totalPosPnl ≥ pnlBurned ∧
       (p.side = .long → m.rawBasisLong ≥ p.rawBasis ∧ newOiL ≤ newRawL) ∧
       (p.side = .short → m.rawBasisShort ≥ p.rawBasis ∧ newOiS ≤ newRawS) ∧
       eff > 0 then
      -- Note: `liqFee` moves from `totalCapital` to `feeSurplus` (or directly paid to liquidator from vault:
      -- in both cases Δ(C + I + S) ≤ ΔV! Here we credit `feeSurplus` to model exact conservation).
      let m' := { m with
        totalCapital  := m.totalCapital - capDeb - liqFee
        insurance     := m.insurance - insDraw
        feeSurplus    := m.feeSurplus + liqFee
        totalPosPnl   := m.totalPosPnl - pnlBurned
        oiLong        := newOiL
        oiShort       := newOiS
        rawBasisLong  := newRawL
        rawBasisShort := newRawS
        adlLong       := newAdlL
        adlShort      := newAdlS }
      some { st with
        markets   := updateFn st.markets mid (some m')
        positions := updateFn st.positions mid (updateFn (st.positions mid) victim (some p2)) }
    else
      none
  else
    none

/-- Permissionless `ForceClosePair` in `WindDown` after `exitWindow` has elapsed:
    Nets any open long against any open short by `q = min(effL, effS) > 0`,
    strictly decreasing `oiLong = oiShort` so no griefer can block market resolution! -/
def stepForceClosePair (st : DexState) (mid longOwner shortOwner curSlot : Nat) : Option DexState := do
  if longOwner = shortOwner then none
  let m ← st.markets mid
  let pL ← st.positions mid longOwner
  let pS ← st.positions mid shortOwner
  if m.status = .windDown ∧ curSlot ≥ m.windDownSlot + m.exitWindow ∧
     pL.side = .long ∧ pS.side = .short ∧
     pL.rawBasis > 0 ∧ pS.rawBasis > 0 then
    let q := min pL.rawBasis (min pS.rawBasis (min m.oiLong m.oiShort))
    if q = 0 ∨ m.rawBasisLong < q ∨ m.rawBasisShort < q then none
    let oiL' := m.oiLong - q
    let oiS' := m.oiShort - q
    let rL'  := m.rawBasisLong - q
    let rS'  := m.rawBasisShort - q
    if oiL' > rL' ∨ oiS' > rS' then none
    let m' := { m with
      oiLong        := oiL'
      oiShort       := oiS'
      rawBasisLong  := rL'
      rawBasisShort := rS'
      adlLong       := deriveAdl oiL' rL'
      adlShort      := deriveAdl oiS' rS' }
    let pL' := { pL with
      rawBasis := pL.rawBasis - q
      side     := if pL.rawBasis = q then .flat else .long }
    let pS' := { pS with
      rawBasis := pS.rawBasis - q
      side     := if pS.rawBasis = q then .flat else .short }
    let mPos1 := updateFn (st.positions mid) longOwner (some pL')
    let mPos2 := updateFn mPos1 shortOwner (some pS')
    some { st with
      markets   := updateFn st.markets mid (some m')
      positions := updateFn st.positions mid mPos2 }
  else
    none

/-- Resolve a `WindDown` market once `oiLong = 0 ∧ oiShort = 0`, freezing an
    order-independent payout snapshot `(resolvedNum, resolvedDen) = (min(R_m, P^+_m), P^+_m)`. -/
def stepResolveMarket (st : DexState) (mid : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status = .windDown ∧ m.oiLong = 0 ∧ m.oiShort = 0 then
    let m' := { m with
      status      := .resolved
      resolvedNum := min m.residual m.totalPosPnl
      resolvedDen := m.totalPosPnl }
    some { st with markets := updateFn st.markets mid (some m') }
  else
    none

/-- Order-independent resolved claim payout formula for a position in a `Resolved` market. -/
def resolvedClaimPayout (m : MarketState) (p : PosState) : Nat :=
  let pnlShare :=
    if m.resolvedDen = 0 then 0
    else (p.pnlTotal * m.resolvedNum) / m.resolvedDen
  p.capital + pnlShare

/-- Permanently tombstone an empty `Resolved` market (`no ABA reuse`). -/
def stepTombstone (st : DexState) (mid : Nat) : Option DexState := do
  let m ← st.markets mid
  if m.status = .resolved ∧ m.oiLong = 0 ∧ m.oiShort = 0 ∧
     m.totalCapital = 0 ∧ m.insurance = 0 ∧ m.activePos = 0 then
    let m' := { m with status := .tombstoned }
    some { st with markets := updateFn st.markets mid (some m') }
  else
    none

end Percolator.Spec
