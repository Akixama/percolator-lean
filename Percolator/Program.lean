/-
  Percolator.Program
  Unified, zero-separation Lean 4 → Solana sBPF perpetual DEX program.
  Written in clean, idiomatic Lean 4 with ZERO manual `@[noinline]` annotations or
  hand-rolled optimizations: `lean-svm` automatically handles smart outlining, constant
  rematerialization, binary-search switch dispatch, load-CSE, and sBPF peephole folding.
-/
import LeanSVM
import Percolator.Layout

namespace Percolator.Program

open LeanSVM
open LeanSVM.Input
open LeanSVM.Math
open LeanSVM.CPI
open Percolator

/-! ### Concise Account & Checked-Mutation Helpers -/

def requireSigner (acc : AccountView) : SolanaM Unit := do
  SolanaM.require (← AccountView.isSigner acc) Err.missingRequiredSignature

def requireWritable (acc : AccountView) : SolanaM Unit := do
  SolanaM.require (← AccountView.isWritable acc) Err.invalidAccountData

def requireKeyEq (a b : Ptr) (err : UInt64) : SolanaM Unit := do
  SolanaM.require (← pubkeyEq a b) err

def requireKeyNe (a b : Ptr) (err : UInt64) : SolanaM Unit := do
  SolanaM.require (!(← pubkeyEq a b)) err

def pubkeyIsZero (p : Ptr) : SolanaM Bool := do
  let w0 ← loadU64 p 0
  let w1 ← loadU64 p 8
  let w2 ← loadU64 p 16
  let w3 ← loadU64 p 24
  return (w0 ||| w1 ||| w2 ||| w3) == 0

def getClockSlot : SolanaM UInt64 := do
  let buf ← stackAlloc 40
  let rc ← sysGetClock buf
  SolanaM.require (rc == 0) Err.invalidAccountData
  loadU64 buf 0

def checkOwnedMagic (acc : AccountView) (progId : Ptr) (minLen : UInt64) (magic : UInt32) : SolanaM Unit := do
  requireKeyEq (AccountView.ownerPtr acc) progId Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen acc) >= minLen) Err.accountDataTooSmall
  SolanaM.require ((← loadU32 (AccountView.dataPtr acc) 0) == magic) PErr.invalidMagic

def checkFreshAccount (acc : AccountView) (progId : Ptr) (minLen : UInt64) : SolanaM Unit := do
  requireWritable acc
  requireKeyEq (AccountView.ownerPtr acc) progId Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen acc) >= minLen) Err.accountDataTooSmall
  SolanaM.require ((← loadU32 (AccountView.dataPtr acc) 0) == 0) Err.accountAlreadyInitialized

def addU64At (base off delta : UInt64) : SolanaM Unit := do
  storeU64 base off (← checkedAdd64 (← loadU64 base off) delta)

def subU64At (base off delta : UInt64) : SolanaM Unit := do
  storeU64 base off (← checkedSub64 (← loadU64 base off) delta)

/-! ### Exact Verified Economic Kernels (Matching `Percolator.Spec` & `Percolator.Proofs`) -/

def deriveAdlU64 (oi rawBasis : UInt64) : SolanaM UInt64 := do
  if rawBasis == 0 || oi >= rawBasis then return ADL_ONE
  let q ← mulDiv64 ADL_ONE oi rawBasis
  return if q == 0 then 1 else q

def haircutPayoutU64 (p residual posPnlTot : UInt64) : SolanaM UInt64 := do
  if posPnlTot == 0 || p == 0 || residual == 0 then return 0
  mulDiv64 p (if residual < posPnlTot then residual else posPnlTot) posPnlTot

def marketResidual (mktData : Ptr) : SolanaM UInt64 := do
  let v ← loadU64 mktData MktOff.vaultBalance
  let ci ← checkedAdd64 (← loadU64 mktData MktOff.totalCapital) (← loadU64 mktData MktOff.insurance)
  checkedSub64 v (← checkedAdd64 ci (← loadU64 mktData MktOff.feeSurplus))

def computeMarginReq (effQty markPrice bps : UInt64) : SolanaM UInt64 := do
  if effQty == 0 then return 0
  mulDiv64Ceil (← mulDiv64Ceil effQty markPrice POS_SCALE) bps BPS_DEN

def posEffectiveQty (mktData posData : Ptr) : SolanaM UInt64 := do
  let side ← loadU8 posData PosOff.side
  let rawB ← loadU64 posData PosOff.rawBasis
  if side == SIDE_FLAT || rawB == 0 then return 0
  let adl ← loadU64 mktData (if side == SIDE_LONG then MktOff.adlLong else MktOff.adlShort)
  mulDiv64 rawB adl ADL_ONE

def checkPosMatchesMarket (mkt pos : AccountView) : SolanaM Unit := do
  let posData := AccountView.dataPtr pos
  requireKeyEq (AccountView.keyPtr mkt) (posData + PosOff.market) PErr.marketMismatch
  SolanaM.require ((← loadU64 (AccountView.dataPtr mkt) MktOff.marketId) == (← loadU64 posData PosOff.marketId)) PErr.marketMismatch

def settlePosition (mktData posData : Ptr) (curSlot : UInt64) : SolanaM UInt64 := do
  let curEpoch := curSlot / (← loadU64 mktData MktOff.warmupSlots)
  let mut pMat  ← loadU64 posData PosOff.pnlMature
  let mut pPrev ← loadU64 posData PosOff.pnlPrev
  let mut pCurr ← loadU64 posData PosOff.pnlCurr
  let pEpoch    ← loadU64 posData PosOff.pnlEpoch

  -- 2-bucket epoch warmup advance (preserves pMat + pPrev + pCurr identically!)
  if curEpoch >= pEpoch + 2 then
    pMat ← checkedAdd64 (← checkedAdd64 pMat pPrev) pCurr
    pPrev := 0; pCurr := 0
    storeU64 posData PosOff.pnlEpoch curEpoch
  else if curEpoch == pEpoch + 1 then
    pMat ← checkedAdd64 pMat pPrev
    pPrev := pCurr; pCurr := 0
    storeU64 posData PosOff.pnlEpoch curEpoch

  let side ← loadU8 posData PosOff.side
  let rawB ← loadU64 posData PosOff.rawBasis
  let mut shortfall : UInt64 := 0

  if side != SIDE_FLAT && rawB > 0 then
    let kSide ← loadU64 mktData (if side == SIDE_LONG then MktOff.kLong else MktOff.kShort)
    let entryK ← loadU64 posData PosOff.entryK
    if kSide > entryK then
      let gain ← mulDiv64 rawB (kSide - entryK) POS_SCALE
      pCurr ← checkedAdd64 pCurr gain
      addU64At mktData MktOff.totalPosPnl gain
    else if entryK > kSide then
      let loss  ← mulDiv64Ceil rawB (entryK - kSide) POS_SCALE
      let bCurr := if loss < pCurr then loss else pCurr
      pCurr := pCurr - bCurr
      let rem1  := loss - bCurr
      let bPrev := if rem1 < pPrev then rem1 else pPrev
      pPrev := pPrev - bPrev
      let rem2  := rem1 - bPrev
      let bMat  := if rem2 < pMat then rem2 else pMat
      pMat := pMat - bMat
      let rem3  := rem2 - bMat
      let pnlBurned ← checkedAdd64 (← checkedAdd64 bCurr bPrev) bMat
      if pnlBurned > 0 then subU64At mktData MktOff.totalPosPnl pnlBurned
      let cap := ← loadU64 posData PosOff.capital
      let capDeb := if rem3 < cap then rem3 else cap
      if capDeb > 0 then
        storeU64 posData PosOff.capital (cap - capDeb)
        subU64At mktData MktOff.totalCapital capDeb
      shortfall := rem3 - capDeb
    storeU64 posData PosOff.entryK kSide

  storeU64 posData PosOff.pnlMature pMat
  storeU64 posData PosOff.pnlPrev   pPrev
  storeU64 posData PosOff.pnlCurr   pCurr
  return shortfall

/-! ### Instruction Handlers (Auto-Outlined by `lean-svm`!) -/

def handleInitProtocol (input : Ptr) : SolanaM Unit := do
  let (prot, admin, feeVault, ix, progId) ← parse3 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner admin
  checkFreshAccount prot progId ProtOff.size
  let createFee ← loadU64 ix.ptr 1
  SolanaM.require (createFee <= MAX_CREATE_FEE) PErr.invalidParams
  let pData := AccountView.dataPtr prot
  storeU32 pData ProtOff.magic MAGIC_PROTOCOL
  storeU8  pData ProtOff.version 1
  pubkeyCopy (pData + ProtOff.admin)    (AccountView.keyPtr admin)
  pubkeyCopy (pData + ProtOff.feeVault) (AccountView.keyPtr feeVault)
  storeU64 pData ProtOff.nextMarketId 1
  storeU64 pData ProtOff.createFee createFee

def handleUpdateCreateFee (input : Ptr) : SolanaM Unit := do
  let (prot, admin, ix, progId) ← parse2 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner admin; requireWritable prot
  checkOwnedMagic prot progId ProtOff.size MAGIC_PROTOCOL
  let pData := AccountView.dataPtr prot
  requireKeyEq (AccountView.keyPtr admin) (pData + ProtOff.admin) PErr.unauthorized
  let newFee ← loadU64 ix.ptr 1
  SolanaM.require (newFee <= MAX_CREATE_FEE) PErr.invalidParams
  storeU64 pData ProtOff.createFee newFee

def handleCreateMarket (input : Ptr) : SolanaM Unit := do
  let (prot, mkt, mint, vaultPda, oracleAuth, creator, creatorTok, feeVaultTok, tokenProg, ix, progId) ← parse9 input
  SolanaM.require (ix.len >= 92) Err.invalidInstructionData
  requireSigner creator; requireWritable prot
  checkOwnedMagic prot progId ProtOff.size MAGIC_PROTOCOL
  checkFreshAccount mkt progId MktOff.size

  let vaultBump     ← loadU8  ix.ptr 1
  let decimals      ← loadU8  ix.ptr 2
  let initPrice     ← loadU64 ix.ptr 4
  let exitWindow    ← loadU64 ix.ptr 12
  let maxStaleness  ← loadU64 ix.ptr 20
  let warmupSlots   ← loadU64 ix.ptr 28
  let imBps         ← loadU64 ix.ptr 36
  let mmBps         ← loadU64 ix.ptr 44
  let liqFeeBps     ← loadU64 ix.ptr 52
  let tradeFeeBps   ← loadU64 ix.ptr 60
  let maxMoveBps    ← loadU64 ix.ptr 68
  let maxInsDrawBps ← loadU64 ix.ptr 76
  let maxOi         ← loadU64 ix.ptr 84

  SolanaM.require (initPrice > 0 && initPrice <= MAX_PRICE) PErr.invalidParams
  SolanaM.require (exitWindow >= MIN_EXIT_WINDOW && maxStaleness >= 1 && warmupSlots >= 1) PErr.invalidParams
  SolanaM.require (mmBps > 0 && mmBps < imBps && imBps <= BPS_DEN) PErr.invalidParams
  SolanaM.require ((← checkedAdd64 maxMoveBps liqFeeBps) <= mmBps) PErr.invalidParams
  SolanaM.require (tradeFeeBps <= 1000 && maxInsDrawBps <= BPS_DEN && maxOi > 0 && maxOi <= MAX_OI) PErr.invalidParams

  let pData := AccountView.dataPtr prot
  let createFee ← loadU64 pData ProtOff.createFee
  if createFee > 0 then
    requireKeyEq (AccountView.keyPtr feeVaultTok) (pData + ProtOff.feeVault) PErr.vaultMismatch
    tokenTransferChecked tokenProg creatorTok mint feeVaultTok creator createFee decimals

  let mid ← loadU64 pData ProtOff.nextMarketId
  storeU64 pData ProtOff.nextMarketId (← checkedAdd64 mid 1)

  let mData := AccountView.dataPtr mkt
  storeU32 mData MktOff.magic MAGIC_MARKET
  storeU8  mData MktOff.status STATUS_ACTIVE
  storeU8  mData MktOff.vaultBump vaultBump
  storeU8  mData MktOff.decimals decimals
  storeU64 mData MktOff.marketId mid
  pubkeyCopy (mData + MktOff.quoteMint)   (AccountView.keyPtr mint)
  pubkeyCopy (mData + MktOff.vaultPda)    (AccountView.keyPtr vaultPda)
  pubkeyCopy (mData + MktOff.oracleAuth)  (AccountView.keyPtr oracleAuth)
  pubkeyCopy (mData + MktOff.marketAdmin) (AccountView.keyPtr creator)
  storeU64 mData MktOff.markPrice initPrice
  storeU64 mData MktOff.lastOracleSlot (← getClockSlot)
  storeU64 mData MktOff.exitWindow exitWindow
  storeU64 mData MktOff.maxStaleness maxStaleness
  storeU64 mData MktOff.warmupSlots warmupSlots
  storeU64 mData MktOff.imBps imBps
  storeU64 mData MktOff.mmBps mmBps
  storeU64 mData MktOff.liqFeeBps liqFeeBps
  storeU64 mData MktOff.tradeFeeBps tradeFeeBps
  storeU64 mData MktOff.maxMoveBps maxMoveBps
  storeU64 mData MktOff.maxInsDrawBps maxInsDrawBps
  storeU64 mData MktOff.maxOi maxOi
  storeU64 mData MktOff.adlLong ADL_ONE
  storeU64 mData MktOff.adlShort ADL_ONE
  storeU64 mData MktOff.kLong K_ZERO
  storeU64 mData MktOff.kShort K_ZERO
  storeU64 mData MktOff.nextPositionId 1

def handleBurnMarketAdmin (input : Ptr) : SolanaM Unit := do
  let (mkt, admin, _, progId) ← parse2 input
  requireSigner admin; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) != STATUS_TOMBSTONED) PErr.invalidStatus
  SolanaM.require (!(← pubkeyIsZero (mData + MktOff.marketAdmin))) PErr.unauthorized
  requireKeyEq (AccountView.keyPtr admin) (mData + MktOff.marketAdmin) PErr.unauthorized
  storeU64 mData (MktOff.marketAdmin + 0)  0
  storeU64 mData (MktOff.marketAdmin + 8)  0
  storeU64 mData (MktOff.marketAdmin + 16) 0
  storeU64 mData (MktOff.marketAdmin + 24) 0

def handleUpdateOracle (input : Ptr) : SolanaM Unit := do
  let (mkt, oracleAuth, ix, progId) ← parse2 input
  SolanaM.require (ix.len >= 18) Err.invalidInstructionData
  requireSigner oracleAuth; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr oracleAuth) (mData + MktOff.oracleAuth) PErr.unauthorized

  let newPrice ← loadU64 ix.ptr 1
  let fundSign ← loadU8  ix.ptr 9
  let fundE6   ← loadU64 ix.ptr 10
  SolanaM.require (newPrice > 0 && newPrice <= MAX_PRICE) PErr.invalidParams

  let oldPrice ← loadU64 mData MktOff.markPrice
  let diff := if newPrice >= oldPrice then newPrice - oldPrice else oldPrice - newPrice
  let maxAllowed ← mulDiv64 oldPrice (← loadU64 mData MktOff.maxMoveBps) BPS_DEN
  SolanaM.require ((← checkedAdd64 diff fundE6) <= maxAllowed) PErr.oracleClamp

  let adlL ← loadU64 mData MktOff.adlLong
  let adlS ← loadU64 mData MktOff.adlShort
  if newPrice > oldPrice then
    addU64At mData MktOff.kLong  (← mulDiv64     adlL diff ADL_ONE)
    subU64At mData MktOff.kShort (← mulDiv64Ceil adlS diff ADL_ONE)
  else if oldPrice > newPrice then
    subU64At mData MktOff.kLong  (← mulDiv64Ceil adlL diff ADL_ONE)
    addU64At mData MktOff.kShort (← mulDiv64     adlS diff ADL_ONE)

  if fundE6 > 0 then
    if fundSign == 0 then
      subU64At mData MktOff.kLong  (← mulDiv64Ceil adlL fundE6 ADL_ONE)
      addU64At mData MktOff.kShort (← mulDiv64     adlS fundE6 ADL_ONE)
    else
      subU64At mData MktOff.kShort (← mulDiv64Ceil adlS fundE6 ADL_ONE)
      addU64At mData MktOff.kLong  (← mulDiv64     adlL fundE6 ADL_ONE)

  storeU64 mData MktOff.markPrice newPrice
  storeU64 mData MktOff.lastOracleSlot (← getClockSlot)

def handleInitPortfolio (input : Ptr) : SolanaM Unit := do
  let (pfl, owner, mint, ix, progId) ← parse3 input
  SolanaM.require (ix.len >= 3) Err.invalidInstructionData
  requireSigner owner
  checkFreshAccount pfl progId PflOff.size
  let fData := AccountView.dataPtr pfl
  storeU32 fData PflOff.magic MAGIC_PORTFOLIO
  storeU8  fData PflOff.vaultBump (← loadU8 ix.ptr 1)
  storeU8  fData PflOff.decimals  (← loadU8 ix.ptr 2)
  pubkeyCopy (fData + PflOff.owner)     (AccountView.keyPtr owner)
  pubkeyCopy (fData + PflOff.quoteMint) (AccountView.keyPtr mint)

def handleDepositPortfolio (input : Ptr) : SolanaM Unit := do
  let (pfl, owner, mint, userTok, pflVault, tokenProg, ix, progId) ← parse6 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable pfl
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mint)  (fData + PflOff.quoteMint) PErr.mintMismatch
  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  tokenTransferChecked tokenProg userTok mint pflVault owner amount (← loadU8 fData PflOff.decimals)
  addU64At fData PflOff.balance amount

def handleWithdrawPortfolio (input : Ptr) : SolanaM Unit := do
  let (pfl, owner, mint, pflVault, userTok, tokenProg, ix, progId) ← parse6 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable pfl
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  let fData := AccountView.dataPtr pfl
  requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mint)  (fData + PflOff.quoteMint) PErr.mintMismatch
  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let bal ← loadU64 fData PflOff.balance
  SolanaM.require (bal >= amount) PErr.insufficientFunds
  storeU64 fData PflOff.balance (bal - amount)
  tokenTransferCheckedSigned tokenProg pflVault mint userTok pflVault amount
    (← loadU8 fData PflOff.decimals) TAG_PFL_VAULT (AccountView.keyPtr pfl) (← loadU8 fData PflOff.vaultBump)

def handleOpenPosition (input : Ptr) : SolanaM Unit := do
  let (mkt, pos, owner, _, progId) ← parse3 input
  requireSigner owner; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  checkFreshAccount pos progId PosOff.size

  let pid ← loadU64 mData MktOff.nextPositionId
  addU64At mData MktOff.nextPositionId 1
  addU64At mData MktOff.activePositions 1

  let pData := AccountView.dataPtr pos
  storeU32 pData PosOff.magic MAGIC_POSITION
  storeU64 pData PosOff.marketId (← loadU64 mData MktOff.marketId)
  storeU64 pData PosOff.positionId pid
  storeU64 pData PosOff.episode 1
  pubkeyCopy (pData + PosOff.owner)  (AccountView.keyPtr owner)
  pubkeyCopy (pData + PosOff.market) (AccountView.keyPtr mkt)
  storeU64 pData PosOff.entryK K_ZERO
  storeU64 pData PosOff.pnlEpoch ((← getClockSlot) / (← loadU64 mData MktOff.warmupSlots))

def handleAllocateMargin (input : Ptr) : SolanaM Unit := do
  let (mkt, pos, pfl, owner, mint, pflVault, mktVault, tokenProg, ix, progId) ← parse8 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable mkt; requireWritable pos; requireWritable pfl
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos progId PosOff.size MAGIC_POSITION
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  checkPosMatchesMarket mkt pos

  let mData := AccountView.dataPtr mkt
  let pData := AccountView.dataPtr pos
  let fData := AccountView.dataPtr pfl
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr owner) (pData + PosOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mint)  (mData + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mint)  (fData + PflOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mktVault) (mData + MktOff.vaultPda) PErr.vaultMismatch

  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let fBal ← loadU64 fData PflOff.balance
  SolanaM.require (fBal >= amount) PErr.insufficientFunds
  tokenTransferCheckedSigned tokenProg pflVault mint mktVault pflVault amount
    (← loadU8 mData MktOff.decimals) TAG_PFL_VAULT (AccountView.keyPtr pfl) (← loadU8 fData PflOff.vaultBump)

  storeU64 fData PflOff.balance (fBal - amount)
  addU64At pData PosOff.capital amount
  addU64At mData MktOff.vaultBalance amount
  addU64At mData MktOff.totalCapital amount

def handleWithdrawMargin (input : Ptr) : SolanaM Unit := do
  let (mkt, pos, pfl, owner, mint, mktVault, pflVault, tokenProg, ix, progId) ← parse8 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable mkt; requireWritable pos; requireWritable pfl
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos progId PosOff.size MAGIC_POSITION
  checkOwnedMagic pfl progId PflOff.size MAGIC_PORTFOLIO
  checkPosMatchesMarket mkt pos

  let mData := AccountView.dataPtr mkt
  let pData := AccountView.dataPtr pos
  let fData := AccountView.dataPtr pfl
  let status ← loadU8 mData MktOff.status
  SolanaM.require (status == STATUS_ACTIVE || status == STATUS_WINDDOWN) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr owner) (pData + PosOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr owner) (fData + PflOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mint)  (mData + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mint)  (fData + PflOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mktVault) (mData + MktOff.vaultPda) PErr.vaultMismatch

  SolanaM.require ((← settlePosition mData pData (← getClockSlot)) == 0) PErr.insufficientMargin
  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let pCap ← loadU64 pData PosOff.capital
  SolanaM.require (pCap >= amount) PErr.insufficientFunds
  let im ← computeMarginReq (← posEffectiveQty mData pData) (← loadU64 mData MktOff.markPrice) (← loadU64 mData MktOff.imBps)
  SolanaM.require (pCap - amount >= im) PErr.insufficientMargin

  tokenTransferCheckedSigned tokenProg mktVault mint pflVault mktVault amount
    (← loadU8 mData MktOff.decimals) TAG_MKT_VAULT (AccountView.keyPtr mkt) (← loadU8 mData MktOff.vaultBump)
  storeU64 pData PosOff.capital (pCap - amount)
  subU64At mData MktOff.vaultBalance amount
  subU64At mData MktOff.totalCapital amount
  addU64At fData PflOff.balance amount

def handleRebalanceMargin (input : Ptr) : SolanaM Unit := do
  let (mkt1, pos1, mkt2, pos2, owner, mint, v1, v2, tokenProg, ix, progId) ← parse9 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner owner; requireWritable mkt1; requireWritable pos1; requireWritable mkt2; requireWritable pos2
  requireKeyNe (AccountView.keyPtr mkt1) (AccountView.keyPtr mkt2) PErr.aliasedAccounts
  requireKeyNe (AccountView.keyPtr pos1) (AccountView.keyPtr pos2) PErr.aliasedAccounts

  checkOwnedMagic mkt1 progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos1 progId PosOff.size MAGIC_POSITION
  checkOwnedMagic mkt2 progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos2 progId PosOff.size MAGIC_POSITION
  checkPosMatchesMarket mkt1 pos1
  checkPosMatchesMarket mkt2 pos2

  let m1Data := AccountView.dataPtr mkt1
  let p1Data := AccountView.dataPtr pos1
  let m2Data := AccountView.dataPtr mkt2
  let p2Data := AccountView.dataPtr pos2
  let st1 ← loadU8 m1Data MktOff.status
  SolanaM.require ((st1 == STATUS_ACTIVE || st1 == STATUS_WINDDOWN) && (← loadU8 m2Data MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr owner) (p1Data + PosOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr owner) (p2Data + PosOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mint)  (m1Data + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mint)  (m2Data + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr v1)    (m1Data + MktOff.vaultPda) PErr.vaultMismatch
  requireKeyEq (AccountView.keyPtr v2)    (m2Data + MktOff.vaultPda) PErr.vaultMismatch

  SolanaM.require ((← settlePosition m1Data p1Data (← getClockSlot)) == 0) PErr.insufficientMargin
  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let cap1 ← loadU64 p1Data PosOff.capital
  SolanaM.require (cap1 >= amount) PErr.insufficientFunds
  let im1 ← computeMarginReq (← posEffectiveQty m1Data p1Data) (← loadU64 m1Data MktOff.markPrice) (← loadU64 m1Data MktOff.imBps)
  SolanaM.require (cap1 - amount >= im1) PErr.insufficientMargin

  tokenTransferCheckedSigned tokenProg v1 mint v2 v1 amount
    (← loadU8 m1Data MktOff.decimals) TAG_MKT_VAULT (AccountView.keyPtr mkt1) (← loadU8 m1Data MktOff.vaultBump)
  storeU64 p1Data PosOff.capital (cap1 - amount)
  subU64At m1Data MktOff.vaultBalance amount
  subU64At m1Data MktOff.totalCapital amount
  addU64At p2Data PosOff.capital amount
  addU64At m2Data MktOff.vaultBalance amount
  addU64At m2Data MktOff.totalCapital amount

def handleDepositInsurance (input : Ptr) : SolanaM Unit := do
  let (mkt, insRec, lp, mint, lpTok, mktVault, tokenProg, ix, progId) ← parse7 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner lp; requireWritable mkt; requireWritable insRec
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET

  let mData := AccountView.dataPtr mkt
  let status ← loadU8 mData MktOff.status
  SolanaM.require (status == STATUS_ACTIVE || status == STATUS_WINDDOWN) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr mint) (mData + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mktVault) (mData + MktOff.vaultPda) PErr.vaultMismatch

  requireKeyEq (AccountView.ownerPtr insRec) progId Err.illegalOwner
  SolanaM.require ((← AccountView.dataLen insRec) >= InsOff.size) Err.accountDataTooSmall
  let rData := AccountView.dataPtr insRec
  let mid ← loadU64 mData MktOff.marketId
  let rMagic ← loadU32 rData InsOff.magic
  if rMagic == 0 then
    storeU32 rData InsOff.magic MAGIC_INSURANCE
    storeU64 rData InsOff.marketId mid
    pubkeyCopy (rData + InsOff.owner)  (AccountView.keyPtr lp)
    pubkeyCopy (rData + InsOff.market) (AccountView.keyPtr mkt)
  else
    SolanaM.require (rMagic == MAGIC_INSURANCE) PErr.invalidMagic
    SolanaM.require ((← loadU64 rData InsOff.marketId) == mid) PErr.marketMismatch
    requireKeyEq (AccountView.keyPtr lp)  (rData + InsOff.owner) PErr.ownerMismatch
    requireKeyEq (AccountView.keyPtr mkt) (rData + InsOff.market) PErr.marketMismatch

  let amount ← loadU64 ix.ptr 1
  SolanaM.require (amount > 0) PErr.invalidParams
  let curIns ← loadU64 mData MktOff.insurance
  let totSh  ← loadU64 mData MktOff.totalInsShares
  let minted ← if totSh == 0 || curIns == 0 then pure amount else mulDiv64 amount totSh curIns
  SolanaM.require (minted > 0) PErr.invalidParams
  tokenTransferChecked tokenProg lpTok mint mktVault lp amount (← loadU8 mData MktOff.decimals)
  addU64At mData MktOff.vaultBalance amount
  addU64At mData MktOff.insurance amount
  addU64At mData MktOff.totalInsShares minted
  addU64At rData InsOff.shares minted

def handleWithdrawInsurance (input : Ptr) : SolanaM Unit := do
  let (mkt, insRec, lp, mint, mktVault, lpTok, tokenProg, ix, progId) ← parse7 input
  SolanaM.require (ix.len >= 9) Err.invalidInstructionData
  requireSigner lp; requireWritable mkt; requireWritable insRec
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic insRec progId InsOff.size MAGIC_INSURANCE

  let mData := AccountView.dataPtr mkt
  let rData := AccountView.dataPtr insRec
  SolanaM.require ((← loadU8 mData MktOff.status) != STATUS_TOMBSTONED) PErr.invalidStatus
  SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0 && (← loadU64 mData MktOff.oiShort) == 0) PErr.nonzeroOi
  SolanaM.require ((← loadU64 rData InsOff.marketId) == (← loadU64 mData MktOff.marketId)) PErr.marketMismatch
  requireKeyEq (AccountView.keyPtr lp)       (rData + InsOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr mkt)      (rData + InsOff.market) PErr.marketMismatch
  requireKeyEq (AccountView.keyPtr mint)     (mData + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mktVault) (mData + MktOff.vaultPda) PErr.vaultMismatch

  let burn ← loadU64 ix.ptr 1
  SolanaM.require (burn > 0) PErr.invalidParams
  let curSh ← loadU64 rData InsOff.shares
  let totSh ← loadU64 mData MktOff.totalInsShares
  SolanaM.require (curSh >= burn && totSh >= burn) PErr.insufficientFunds
  let pay ← mulDiv64 burn (← loadU64 mData MktOff.insurance) totSh
  if pay > 0 then
    tokenTransferCheckedSigned tokenProg mktVault mint lpTok mktVault pay
      (← loadU8 mData MktOff.decimals) TAG_MKT_VAULT (AccountView.keyPtr mkt) (← loadU8 mData MktOff.vaultBump)
  storeU64 rData InsOff.shares (curSh - burn)
  storeU64 mData MktOff.totalInsShares (totSh - burn)
  subU64At mData MktOff.insurance pay
  subU64At mData MktOff.vaultBalance pay

def applyExecDiffAndFees (mData lData sData qty execPrice : UInt64) : SolanaM Unit := do
  let markP ← loadU64 mData MktOff.markPrice
  let pDiff := if execPrice >= markP then execPrice - markP else markP - execPrice
  SolanaM.require (pDiff <= (← mulDiv64 markP (← loadU64 mData MktOff.maxMoveBps) BPS_DEN)) PErr.oracleClamp

  if execPrice > markP then
    let payUp   ← mulDiv64Ceil qty (execPrice - markP) POS_SCALE
    let rcvDown ← mulDiv64     qty (execPrice - markP) POS_SCALE
    let capL ← loadU64 lData PosOff.capital
    SolanaM.require (capL >= payUp) PErr.insufficientMargin
    storeU64 lData PosOff.capital (capL - payUp)
    addU64At sData PosOff.capital rcvDown
    let res := payUp - rcvDown
    if res > 0 then subU64At mData MktOff.totalCapital res; addU64At mData MktOff.feeSurplus res
  else if markP > execPrice then
    let payUp   ← mulDiv64Ceil qty (markP - execPrice) POS_SCALE
    let rcvDown ← mulDiv64     qty (markP - execPrice) POS_SCALE
    let capS ← loadU64 sData PosOff.capital
    SolanaM.require (capS >= payUp) PErr.insufficientMargin
    storeU64 sData PosOff.capital (capS - payUp)
    addU64At lData PosOff.capital rcvDown
    let res := payUp - rcvDown
    if res > 0 then subU64At mData MktOff.totalCapital res; addU64At mData MktOff.feeSurplus res

  let feeEach ← mulDiv64Ceil (← mulDiv64Ceil qty execPrice POS_SCALE) (← loadU64 mData MktOff.tradeFeeBps) BPS_DEN
  let capL ← loadU64 lData PosOff.capital
  let capS ← loadU64 sData PosOff.capital
  let feeL := if feeEach < capL then feeEach else capL
  let feeS := if feeEach < capS then feeEach else capS
  storeU64 lData PosOff.capital (capL - feeL)
  storeU64 sData PosOff.capital (capS - feeS)
  let totFee ← checkedAdd64 feeL feeS
  subU64At mData MktOff.totalCapital totFee
  addU64At mData MktOff.insurance totFee

def handleTrade (input : Ptr) : SolanaM Unit := do
  let (mkt, posL, posS, ownL, ownS, ix, progId) ← parse5 input
  SolanaM.require (ix.len >= 18) Err.invalidInstructionData
  requireSigner ownL; requireSigner ownS; requireWritable mkt; requireWritable posL; requireWritable posS
  requireKeyNe (AccountView.keyPtr posL) (AccountView.keyPtr posS) PErr.aliasedAccounts
  checkOwnedMagic mkt  progId MktOff.size MAGIC_MARKET
  checkOwnedMagic posL progId PosOff.size MAGIC_POSITION
  checkOwnedMagic posS progId PosOff.size MAGIC_POSITION
  checkPosMatchesMarket mkt posL
  checkPosMatchesMarket mkt posS

  let mData := AccountView.dataPtr mkt
  let lData := AccountView.dataPtr posL
  let sData := AccountView.dataPtr posS
  requireKeyEq (AccountView.keyPtr ownL) (lData + PosOff.owner) PErr.ownerMismatch
  requireKeyEq (AccountView.keyPtr ownS) (sData + PosOff.owner) PErr.ownerMismatch

  let qty       ← loadU64 ix.ptr 1
  let execPrice ← loadU64 ix.ptr 9
  let mode      ← loadU8  ix.ptr 17
  SolanaM.require (qty > 0 && execPrice > 0 && execPrice <= MAX_PRICE) PErr.invalidParams

  let curSlot ← getClockSlot
  SolanaM.require ((← settlePosition mData lData curSlot) == 0) PErr.insufficientMargin
  SolanaM.require ((← settlePosition mData sData curSlot) == 0) PErr.insufficientMargin
  applyExecDiffAndFees mData lData sData qty execPrice

  let status ← loadU8  mData MktOff.status
  let sideL  ← loadU8  lData PosOff.side
  let sideS  ← loadU8  sData PosOff.side
  let rawL   ← loadU64 lData PosOff.rawBasis
  let rawS   ← loadU64 sData PosOff.rawBasis
  let oiL    ← loadU64 mData MktOff.oiLong
  let oiS    ← loadU64 mData MktOff.oiShort

  if mode == 0 then
    SolanaM.require (status == STATUS_ACTIVE) PErr.invalidStatus
    SolanaM.require (curSlot <= (← loadU64 mData MktOff.lastOracleSlot) + (← loadU64 mData MktOff.maxStaleness)) PErr.oracleStale
    SolanaM.require ((← loadU64 mData MktOff.adlLong) == ADL_ONE && (← loadU64 mData MktOff.adlShort) == ADL_ONE) PErr.adlHaircutActive
    SolanaM.require ((sideL == SIDE_FLAT || sideL == SIDE_LONG) && (sideS == SIDE_FLAT || sideS == SIDE_SHORT)) PErr.invalidSide
    let maxOi ← loadU64 mData MktOff.maxOi
    let newOiL ← checkedAdd64 oiL qty
    let newOiS ← checkedAdd64 oiS qty
    SolanaM.require (newOiL <= maxOi && newOiS <= maxOi) PErr.oiLimitExceeded
    let newRawL ← checkedAdd64 rawL qty
    let newRawS ← checkedAdd64 rawS qty
    let markP ← loadU64 mData MktOff.markPrice
    let imBps ← loadU64 mData MktOff.imBps
    SolanaM.require ((← loadU64 lData PosOff.capital) >= (← computeMarginReq newRawL markP imBps)) PErr.insufficientMargin
    SolanaM.require ((← loadU64 sData PosOff.capital) >= (← computeMarginReq newRawS markP imBps)) PErr.insufficientMargin
    storeU8  lData PosOff.side SIDE_LONG
    storeU8  sData PosOff.side SIDE_SHORT
    storeU64 lData PosOff.rawBasis newRawL
    storeU64 sData PosOff.rawBasis newRawS
    storeU64 lData PosOff.entryK (← loadU64 mData MktOff.kLong)
    storeU64 sData PosOff.entryK (← loadU64 mData MktOff.kShort)
    storeU64 mData MktOff.oiLong newOiL
    storeU64 mData MktOff.oiShort newOiS
    addU64At mData MktOff.rawBasisLong qty
    addU64At mData MktOff.rawBasisShort qty
  else
    SolanaM.require (status == STATUS_ACTIVE || status == STATUS_WINDDOWN) PErr.invalidStatus
    SolanaM.require (sideL == SIDE_LONG && sideS == SIDE_SHORT && rawL >= qty && rawS >= qty) PErr.invalidSide
    let rbL ← loadU64 mData MktOff.rawBasisLong
    let rbS ← loadU64 mData MktOff.rawBasisShort
    SolanaM.require (oiL >= qty && oiS >= qty && rbL >= qty && rbS >= qty) PErr.invalidParams
    let newOiL := oiL - qty; let newOiS := oiS - qty
    let newRbL := rbL - qty; let newRbS := rbS - qty
    SolanaM.require (newOiL <= newRbL && newOiS <= newRbS) PErr.invalidParams
    storeU8  lData PosOff.side (if rawL == qty then SIDE_FLAT else SIDE_LONG)
    storeU8  sData PosOff.side (if rawS == qty then SIDE_FLAT else SIDE_SHORT)
    storeU64 lData PosOff.rawBasis (rawL - qty)
    storeU64 sData PosOff.rawBasis (rawS - qty)
    storeU64 mData MktOff.oiLong newOiL
    storeU64 mData MktOff.oiShort newOiS
    storeU64 mData MktOff.rawBasisLong newRbL
    storeU64 mData MktOff.rawBasisShort newRbS
    storeU64 mData MktOff.adlLong  (← deriveAdlU64 newOiL newRbL)
    storeU64 mData MktOff.adlShort (← deriveAdlU64 newOiS newRbS)

  addU64At lData PosOff.episode 1
  addU64At sData PosOff.episode 1

def handleSettleAndRealize (input : Ptr) : SolanaM Unit := do
  let (mkt, pos, owner, _, progId) ← parse3 input
  requireSigner owner; requireWritable mkt; requireWritable pos
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos progId PosOff.size MAGIC_POSITION
  checkPosMatchesMarket mkt pos

  let mData := AccountView.dataPtr mkt
  let pData := AccountView.dataPtr pos
  let status ← loadU8 mData MktOff.status
  SolanaM.require (status == STATUS_ACTIVE || status == STATUS_WINDDOWN) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr owner) (pData + PosOff.owner) PErr.ownerMismatch

  let _ ← settlePosition mData pData (← getClockSlot)
  let pMat ← loadU64 pData PosOff.pnlMature
  if pMat > 0 then
    let totPnl ← loadU64 mData MktOff.totalPosPnl
    SolanaM.require (totPnl >= pMat) Err.arithmeticOverflow
    let pay ← haircutPayoutU64 pMat (← marketResidual mData) totPnl
    storeU64 pData PosOff.pnlMature 0
    storeU64 mData MktOff.totalPosPnl (totPnl - pMat)
    if pay > 0 then
      addU64At pData PosOff.capital pay
      addU64At mData MktOff.totalCapital pay

def handleLiquidate (input : Ptr) : SolanaM Unit := do
  let (mkt, pos, liqTok, mint, mktVault, tokenProg, keeper, _, progId) ← parse7 input
  requireSigner keeper; requireWritable mkt; requireWritable pos
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos progId PosOff.size MAGIC_POSITION
  checkPosMatchesMarket mkt pos

  let mData := AccountView.dataPtr mkt
  let pData := AccountView.dataPtr pos
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  requireKeyEq (AccountView.keyPtr mint)     (mData + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mktVault) (mData + MktOff.vaultPda)  PErr.vaultMismatch

  let side ← loadU8  pData PosOff.side
  let rawB ← loadU64 pData PosOff.rawBasis
  SolanaM.require (side != SIDE_FLAT && rawB > 0) PErr.invalidSide

  let shortfall ← settlePosition mData pData (← getClockSlot)
  let cap   ← loadU64 pData PosOff.capital
  let eff   ← posEffectiveQty mData pData
  let markP ← loadU64 mData MktOff.markPrice
  SolanaM.require (shortfall > 0 || cap < (← computeMarginReq eff markP (← loadU64 mData MktOff.mmBps))) PErr.positionHealthy

  let liqFeeRaw ← mulDiv64 (← mulDiv64Ceil eff markP POS_SCALE) (← loadU64 mData MktOff.liqFeeBps) BPS_DEN
  let liqFee := if liqFeeRaw < cap then liqFeeRaw else cap
  if liqFee > 0 then
    tokenTransferCheckedSigned tokenProg mktVault mint liqTok mktVault liqFee
      (← loadU8 mData MktOff.decimals) TAG_MKT_VAULT (AccountView.keyPtr mkt) (← loadU8 mData MktOff.vaultBump)
    storeU64 pData PosOff.capital (cap - liqFee)
    subU64At mData MktOff.totalCapital liqFee
    subU64At mData MktOff.vaultBalance liqFee

  if shortfall > 0 then
    let ins ← loadU64 mData MktOff.insurance
    let maxDraw ← mulDiv64 ins (← loadU64 mData MktOff.maxInsDrawBps) BPS_DEN
    let capDraw := if maxDraw < ins then maxDraw else ins
    let insDraw := if shortfall < capDraw then shortfall else capDraw
    if insDraw > 0 then storeU64 mData MktOff.insurance (ins - insDraw)

  let oiL ← loadU64 mData MktOff.oiLong
  let oiS ← loadU64 mData MktOff.oiShort
  let minOi := if oiL < oiS then oiL else oiS
  let closeEff := if eff < minOi then eff else minOi
  let newRbL ← if side == SIDE_LONG  then checkedSub64 (← loadU64 mData MktOff.rawBasisLong)  rawB else loadU64 mData MktOff.rawBasisLong
  let newRbS ← if side == SIDE_SHORT then checkedSub64 (← loadU64 mData MktOff.rawBasisShort) rawB else loadU64 mData MktOff.rawBasisShort
  let adjL := if oiL - closeEff > newRbL then newRbL else oiL - closeEff
  let adjS := if oiS - closeEff > newRbS then newRbS else oiS - closeEff
  let finalOi := if adjL < adjS then adjL else adjS

  storeU8  pData PosOff.side SIDE_FLAT
  storeU64 pData PosOff.rawBasis 0
  addU64At pData PosOff.episode 1
  storeU64 mData MktOff.oiLong finalOi
  storeU64 mData MktOff.oiShort finalOi
  storeU64 mData MktOff.rawBasisLong newRbL
  storeU64 mData MktOff.rawBasisShort newRbS
  storeU64 mData MktOff.adlLong  (← deriveAdlU64 finalOi newRbL)
  storeU64 mData MktOff.adlShort (← deriveAdlU64 finalOi newRbS)

def handleStartWindDown (input : Ptr) : SolanaM Unit := do
  let (mkt, caller, _, progId) ← parse2 input
  requireSigner caller; requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_ACTIVE) PErr.invalidStatus
  let curSlot ← getClockSlot
  if curSlot < (← loadU64 mData MktOff.lastOracleSlot) + (← loadU64 mData MktOff.maxStaleness) then
    SolanaM.require (!(← pubkeyIsZero (mData + MktOff.marketAdmin))) PErr.oracleNotStale
    requireKeyEq (AccountView.keyPtr caller) (mData + MktOff.marketAdmin) PErr.unauthorized
  storeU8  mData MktOff.status STATUS_WINDDOWN
  storeU64 mData MktOff.windDownSlot curSlot

def handleForceClosePair (input : Ptr) : SolanaM Unit := do
  let (mkt, posL, posS, _, progId) ← parse3 input
  requireWritable mkt; requireWritable posL; requireWritable posS
  requireKeyNe (AccountView.keyPtr posL) (AccountView.keyPtr posS) PErr.aliasedAccounts
  checkOwnedMagic mkt  progId MktOff.size MAGIC_MARKET
  checkOwnedMagic posL progId PosOff.size MAGIC_POSITION
  checkOwnedMagic posS progId PosOff.size MAGIC_POSITION
  checkPosMatchesMarket mkt posL
  checkPosMatchesMarket mkt posS

  let mData := AccountView.dataPtr mkt
  let lData := AccountView.dataPtr posL
  let sData := AccountView.dataPtr posS
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_WINDDOWN) PErr.invalidStatus
  let curSlot ← getClockSlot
  SolanaM.require (curSlot >= (← loadU64 mData MktOff.windDownSlot) + (← loadU64 mData MktOff.exitWindow)) PErr.exitWindowActive
  SolanaM.require ((← loadU8 lData PosOff.side) == SIDE_LONG && (← loadU8 sData PosOff.side) == SIDE_SHORT) PErr.invalidSide
  let _ ← settlePosition mData lData curSlot
  let _ ← settlePosition mData sData curSlot

  let rawL ← loadU64 lData PosOff.rawBasis
  let rawS ← loadU64 sData PosOff.rawBasis
  let oiL  ← loadU64 mData MktOff.oiLong
  let oiS  ← loadU64 mData MktOff.oiShort
  let q1 := if rawL < rawS then rawL else rawS
  let q2 := if oiL < oiS then oiL else oiS
  let q  := if q1 < q2 then q1 else q2
  SolanaM.require (q > 0) PErr.invalidParams

  let newOiL := oiL - q; let newOiS := oiS - q
  let newRbL ← checkedSub64 (← loadU64 mData MktOff.rawBasisLong) q
  let newRbS ← checkedSub64 (← loadU64 mData MktOff.rawBasisShort) q
  SolanaM.require (newOiL <= newRbL && newOiS <= newRbS) PErr.invalidParams

  storeU8  lData PosOff.side (if rawL == q then SIDE_FLAT else SIDE_LONG)
  storeU8  sData PosOff.side (if rawS == q then SIDE_FLAT else SIDE_SHORT)
  storeU64 lData PosOff.rawBasis (rawL - q)
  storeU64 sData PosOff.rawBasis (rawS - q)
  storeU64 mData MktOff.oiLong newOiL
  storeU64 mData MktOff.oiShort newOiS
  storeU64 mData MktOff.rawBasisLong newRbL
  storeU64 mData MktOff.rawBasisShort newRbS
  storeU64 mData MktOff.adlLong  (← deriveAdlU64 newOiL newRbL)
  storeU64 mData MktOff.adlShort (← deriveAdlU64 newOiS newRbS)

def handleResolveMarket (input : Ptr) : SolanaM Unit := do
  let (mkt, _, progId) ← parse1 input
  requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_WINDDOWN) PErr.invalidStatus
  SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0 && (← loadU64 mData MktOff.oiShort) == 0) PErr.nonzeroOi
  let res ← marketResidual mData
  let totPnl ← loadU64 mData MktOff.totalPosPnl
  storeU8  mData MktOff.status STATUS_RESOLVED
  storeU64 mData MktOff.resolvedNum (if res < totPnl then res else totPnl)
  storeU64 mData MktOff.resolvedDen totPnl

def handleClaimResolved (input : Ptr) : SolanaM Unit := do
  let (mkt, pos, ownerTok, mint, mktVault, tokenProg, caller, _, progId) ← parse7 input
  requireSigner caller; requireWritable mkt; requireWritable pos
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  checkOwnedMagic pos progId PosOff.size MAGIC_POSITION
  checkPosMatchesMarket mkt pos

  let mData := AccountView.dataPtr mkt
  let pData := AccountView.dataPtr pos
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_RESOLVED) PErr.invalidStatus
  SolanaM.require ((← loadU8 pData PosOff.claimed) == 0) PErr.alreadyClaimed
  requireKeyEq (AccountView.keyPtr mint)     (mData + MktOff.quoteMint) PErr.mintMismatch
  requireKeyEq (AccountView.keyPtr mktVault) (mData + MktOff.vaultPda)  PErr.vaultMismatch
  requireKeyEq (AccountView.dataPtr ownerTok + 32) (pData + PosOff.owner) PErr.ownerMismatch

  if !(← pubkeyEq (AccountView.keyPtr caller) (pData + PosOff.owner)) then
    SolanaM.require ((← getClockSlot) >= (← loadU64 mData MktOff.windDownSlot) + (← loadU64 mData MktOff.exitWindow)) PErr.exitWindowActive

  let cap  ← loadU64 pData PosOff.capital
  let pTot ← checkedAdd64 (← checkedAdd64 (← loadU64 pData PosOff.pnlMature) (← loadU64 pData PosOff.pnlPrev))
                          (← loadU64 pData PosOff.pnlCurr)
  let rDen ← loadU64 mData MktOff.resolvedDen
  let pnlShare ← if rDen == 0 || pTot == 0 then pure 0
                 else mulDiv64 pTot (← loadU64 mData MktOff.resolvedNum) rDen
  let totalPay ← checkedAdd64 cap pnlShare
  if totalPay > 0 then
    tokenTransferCheckedSigned tokenProg mktVault mint ownerTok mktVault totalPay
      (← loadU8 mData MktOff.decimals) TAG_MKT_VAULT (AccountView.keyPtr mkt) (← loadU8 mData MktOff.vaultBump)

  storeU8  pData PosOff.claimed 1
  storeU64 pData PosOff.capital 0
  storeU64 pData PosOff.pnlMature 0
  storeU64 pData PosOff.pnlPrev 0
  storeU64 pData PosOff.pnlCurr 0
  subU64At mData MktOff.totalCapital cap
  subU64At mData MktOff.totalPosPnl pTot
  subU64At mData MktOff.vaultBalance totalPay
  subU64At mData MktOff.activePositions 1

def handleTombstoneMarket (input : Ptr) : SolanaM Unit := do
  let (mkt, _, progId) ← parse1 input
  requireWritable mkt
  checkOwnedMagic mkt progId MktOff.size MAGIC_MARKET
  let mData := AccountView.dataPtr mkt
  SolanaM.require ((← loadU8 mData MktOff.status) == STATUS_RESOLVED) PErr.invalidStatus
  SolanaM.require ((← loadU64 mData MktOff.oiLong) == 0 && (← loadU64 mData MktOff.oiShort) == 0 &&
                   (← loadU64 mData MktOff.totalCapital) == 0 && (← loadU64 mData MktOff.insurance) == 0 &&
                   (← loadU64 mData MktOff.activePositions) == 0) PErr.nonzeroState
  storeU8 mData MktOff.status STATUS_TOMBSTONED

/-! ### Main Unified Solana Entrypoint (Auto-Compiled to Balanced Binary-Search Dispatch!) -/

def entrypoint (input : Ptr) : SolanaM Unit := do
  let (_, _, ix, _) ← parseIxOnly input
  SolanaM.require (ix.len >= 1) Err.invalidInstructionData
  match ← loadU8 ix.ptr 0 with
  | 0  => handleInitProtocol input
  | 1  => handleUpdateCreateFee input
  | 2  => handleCreateMarket input
  | 3  => handleBurnMarketAdmin input
  | 4  => handleUpdateOracle input
  | 5  => handleInitPortfolio input
  | 6  => handleDepositPortfolio input
  | 7  => handleWithdrawPortfolio input
  | 8  => handleOpenPosition input
  | 9  => handleAllocateMargin input
  | 10 => handleWithdrawMargin input
  | 11 => handleRebalanceMargin input
  | 12 => handleDepositInsurance input
  | 13 => handleWithdrawInsurance input
  | 14 => handleTrade input
  | 15 => handleSettleAndRealize input
  | 16 => handleLiquidate input
  | 17 => handleStartWindDown input
  | 18 => handleForceClosePair input
  | 19 => handleResolveMarket input
  | 20 => handleClaimResolved input
  | 21 => handleTombstoneMarket input
  | _  => SolanaM.fail PErr.invalidInstruction

end Percolator.Program
