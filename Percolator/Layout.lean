/-
  Percolator.Layout
  Shared constants, error codes, and exact zero-copy byte layouts for `percolator-lean`.
  No engine/program separation: the exact same constants and offsets are used by both
  the formal Lean 4 specification/proofs and the compiled Solana sBPF entrypoint.
-/
import LeanSVM

namespace Percolator

/-! ### Protocol Scales & Hard Bounds -/

def POS_SCALE        : UInt64 := 1_000_000         -- 10^6 (size & price fixed-point scale)
def ADL_ONE          : UInt64 := 1_000_000_000     -- 10^9 (derived side ADL index scale)
def BPS_DEN          : UInt64 := 10_000            -- basis points denominator
def K_ZERO           : UInt64 := 0x4000000000000000 -- 2^62 unbiased zero for cumulative K_side
def MAX_PRICE        : UInt64 := 1_000_000_000_000 -- $1,000,000 at E6
def MAX_OI           : UInt64 := 10_000_000_000_000 -- 10,000,000 units at E6
def MAX_CREATE_FEE   : UInt64 := 10_000_000_000    -- 10,000 quote units at E6
def MIN_EXIT_WINDOW  : UInt64 := 10                -- minimum mandatory wind-down exit window (slots)

/-! ### Account Type Magics (4-byte little-endian ASCII) -/

def MAGIC_PROTOCOL   : UInt32 := 0x544F5250        -- "PROT"
def MAGIC_MARKET     : UInt32 := 0x50544B4D        -- "MKTP"
def MAGIC_POSITION   : UInt32 := 0x50534F50        -- "POSP"
def MAGIC_PORTFOLIO  : UInt32 := 0x4F4C4650        -- "PFLO"
def MAGIC_INSURANCE  : UInt32 := 0x52534E49        -- "INSR"

/-! ### PDA Seed Tags (4-byte little-endian ASCII for `tokenTransferCheckedSigned`) -/

def TAG_MKT_VAULT    : UInt32 := 0x746C766D        -- "mvlt"
def TAG_PFL_VAULT    : UInt32 := 0x746C7670        -- "pvlt"

/-! ### Market Lifecycle Statuses -/

def STATUS_ACTIVE     : UInt8 := 0
def STATUS_WINDDOWN   : UInt8 := 1
def STATUS_RESOLVED   : UInt8 := 2
def STATUS_TOMBSTONED : UInt8 := 3

/-! ### Position Sides -/

def SIDE_FLAT  : UInt8 := 0
def SIDE_LONG  : UInt8 := 1
def SIDE_SHORT : UInt8 := 2

/-! ### Program Error Codes (custom >= 100) -/

namespace PErr
  def invalidMagic       : UInt64 := 100
  def invalidStatus      : UInt64 := 101
  def unauthorized       : UInt64 := 102
  def invalidParams      : UInt64 := 103
  def oracleClamp        : UInt64 := 104
  def oracleNotStale     : UInt64 := 105
  def oracleStale        : UInt64 := 106
  def insufficientMargin : UInt64 := 107
  def insufficientFunds  : UInt64 := 108
  def aliasedAccounts    : UInt64 := 109
  def marketMismatch     : UInt64 := 110
  def ownerMismatch      : UInt64 := 111
  def mintMismatch       : UInt64 := 112
  def vaultMismatch      : UInt64 := 113
  def oiLimitExceeded    : UInt64 := 114
  def adlHaircutActive   : UInt64 := 115
  def positionHealthy    : UInt64 := 116
  def exitWindowActive   : UInt64 := 117
  def nonzeroOi          : UInt64 := 118
  def nonzeroState       : UInt64 := 119
  def alreadyClaimed     : UInt64 := 120
  def invalidSide        : UInt64 := 121
  def nothingToRealize   : UInt64 := 122
  def invalidInstruction : UInt64 := 123
end PErr

/-! ### Exact Byte Offsets: `ProtocolConfig` (88 bytes) -/

namespace ProtOff
  def size          : UInt64 := 88
  def magic         : UInt64 := 0   -- u32
  def version       : UInt64 := 4   -- u8
  def admin         : UInt64 := 8   -- Pubkey (32)
  def feeVault      : UInt64 := 40  -- Pubkey (32)
  def nextMarketId  : UInt64 := 72  -- u64
  def createFee     : UInt64 := 80  -- u64
end ProtOff

/-! ### Exact Byte Offsets: `Market` (392 bytes) -/

namespace MktOff
  def size            : UInt64 := 392
  def magic           : UInt64 := 0   -- u32
  def status          : UInt64 := 4   -- u8
  def vaultBump       : UInt64 := 5   -- u8
  def decimals        : UInt64 := 6   -- u8
  def marketId        : UInt64 := 8   -- u64
  def quoteMint       : UInt64 := 16  -- Pubkey (32)
  def vaultPda        : UInt64 := 48  -- Pubkey (32)
  def oracleAuth      : UInt64 := 80  -- Pubkey (32)
  def marketAdmin     : UInt64 := 112 -- Pubkey (32)
  def markPrice       : UInt64 := 144 -- u64 (E6)
  def lastOracleSlot  : UInt64 := 152 -- u64
  def windDownSlot    : UInt64 := 160 -- u64
  def exitWindow      : UInt64 := 168 -- u64
  def maxStaleness    : UInt64 := 176 -- u64
  def warmupSlots     : UInt64 := 184 -- u64
  def imBps           : UInt64 := 192 -- u64
  def mmBps           : UInt64 := 200 -- u64
  def liqFeeBps       : UInt64 := 208 -- u64
  def tradeFeeBps     : UInt64 := 216 -- u64
  def maxMoveBps      : UInt64 := 224 -- u64
  def maxInsDrawBps   : UInt64 := 232 -- u64
  def maxOi           : UInt64 := 240 -- u64
  def vaultBalance    : UInt64 := 248 -- u64 (V_m)
  def totalCapital    : UInt64 := 256 -- u64 (C_m)
  def insurance       : UInt64 := 264 -- u64 (I_m)
  def feeSurplus      : UInt64 := 272 -- u64 (S_m)
  def totalPosPnl     : UInt64 := 280 -- u64 (P^+_m)
  def totalInsShares  : UInt64 := 288 -- u64
  def oiLong          : UInt64 := 296 -- u64
  def oiShort         : UInt64 := 304 -- u64
  def rawBasisLong    : UInt64 := 312 -- u64
  def rawBasisShort   : UInt64 := 320 -- u64
  def adlLong         : UInt64 := 328 -- u64
  def adlShort        : UInt64 := 336 -- u64
  def kLong           : UInt64 := 344 -- u64 (biased by K_ZERO)
  def kShort          : UInt64 := 352 -- u64 (biased by K_ZERO)
  def resolvedNum     : UInt64 := 360 -- u64
  def resolvedDen     : UInt64 := 368 -- u64
  def activePositions : UInt64 := 376 -- u64
  def nextPositionId  : UInt64 := 384 -- u64
end MktOff

/-! ### Exact Byte Offsets: `Position` (152 bytes) -/

namespace PosOff
  def size       : UInt64 := 152
  def magic      : UInt64 := 0   -- u32
  def side       : UInt64 := 4   -- u8
  def claimed    : UInt64 := 5   -- u8
  def marketId   : UInt64 := 8   -- u64
  def positionId : UInt64 := 16  -- u64
  def episode    : UInt64 := 24  -- u64
  def owner      : UInt64 := 32  -- Pubkey (32)
  def market     : UInt64 := 64  -- Pubkey (32)
  def capital    : UInt64 := 96  -- u64
  def rawBasis   : UInt64 := 104 -- u64
  def entryK     : UInt64 := 112 -- u64
  def pnlMature  : UInt64 := 120 -- u64
  def pnlPrev    : UInt64 := 128 -- u64
  def pnlCurr    : UInt64 := 136 -- u64
  def pnlEpoch   : UInt64 := 144 -- u64
end PosOff

/-! ### Exact Byte Offsets: `Portfolio` (88 bytes) -/

namespace PflOff
  def size       : UInt64 := 88
  def magic      : UInt64 := 0   -- u32
  def vaultBump  : UInt64 := 4   -- u8
  def decimals   : UInt64 := 5   -- u8
  def owner      : UInt64 := 8   -- Pubkey (32)
  def quoteMint  : UInt64 := 40  -- Pubkey (32)
  def balance    : UInt64 := 72  -- u64
  def nonce      : UInt64 := 80  -- u64
end PflOff

/-! ### Exact Byte Offsets: `InsReceipt` (88 bytes) -/

namespace InsOff
  def size      : UInt64 := 88
  def magic     : UInt64 := 0   -- u32
  def marketId  : UInt64 := 8   -- u64
  def owner     : UInt64 := 16  -- Pubkey (32)
  def market    : UInt64 := 48  -- Pubkey (32)
  def shares    : UInt64 := 80  -- u64
end InsOff

/-! ### Instruction Opcodes (1-byte tag at ix[0]) -/

namespace IxOp
  def initProtocol      : UInt8 := 0
  def updateCreateFee   : UInt8 := 1
  def createMarket      : UInt8 := 2
  def burnMarketAdmin   : UInt8 := 3
  def updateOracle      : UInt8 := 4
  def initPortfolio     : UInt8 := 5
  def depositPortfolio  : UInt8 := 6
  def withdrawPortfolio : UInt8 := 7
  def openPosition      : UInt8 := 8
  def allocateMargin    : UInt8 := 9
  def withdrawMargin    : UInt8 := 10
  def rebalanceMargin   : UInt8 := 11
  def depositInsurance  : UInt8 := 12
  def withdrawInsurance : UInt8 := 13
  def trade             : UInt8 := 14
  def settleAndRealize  : UInt8 := 15
  def liquidate         : UInt8 := 16
  def startWindDown     : UInt8 := 17
  def forceClosePair    : UInt8 := 18
  def resolveMarket     : UInt8 := 19
  def claimResolved     : UInt8 := 20
  def tombstoneMarket   : UInt8 := 21
end IxOp

end Percolator
