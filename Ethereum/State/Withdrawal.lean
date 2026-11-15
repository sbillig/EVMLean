-- Requires the following python packages: pycryptodome

import Ethereum.Wheels
import Ethereum.Maps.AccountMap
import Conform.Wheels
import Ethereum.Exception

import Ethereum.Trie

open Ethereum ByteArray

/--
EIP-4895: Beacon chain push withdrawals as operations.
- `index` - starting from `0`
- `validator_index`
- `address` - a recipient for the withdrawn ether
- `amount` - a nonzero amount of ether given in Gwei
-/
structure Withdrawal where
  index : UInt64
  validatorIndex : UInt64
  address : AccountAddress
  amount : UInt64
deriving Repr, BEq

namespace Withdrawal

def to𝕋 : Withdrawal → 𝕋
  | {index, validatorIndex, address, amount} =>
    .𝕃
      [ .𝔹 (BE index.toFin.val)
      , .𝔹 (BE validatorIndex.toFin.val)
      , .𝔹 (address.toByteArray)
      , .𝔹 (BE amount.toFin.val)
      ]

end Withdrawal

/-- The `i`-th withdrawal's entry in the withdrawal trie (EIP-4895): the RLP of `i`, and the
withdrawal's encoding. -/
def Withdrawal.trieEntry (w : ℕ × ByteArray) : Option (ByteArray × ByteArray) := do
  pure (← RLP (.𝔹 (BE w.1)), w.2)

-- EIP-4895
def Withdrawal.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  trieRoot (← ((Array.range ws.size).zip ws).mapM Withdrawal.trieEntry)

def applyWithdrawals
  (σ : AccountMap)
  (ws : Array Withdrawal)
    :
  AccountMap
:=
  ws.foldl applyWithdrawal σ
 where
  applyWithdrawal (σ : AccountMap) (w : Withdrawal) : AccountMap :=
    if w.amount <= 0 then σ else
      match σ.get? w.address with
        | none =>
          σ.insert w.address {(default : Account) with balance := .ofNat <| w.amount.toFin.val * 10^9}
        | some ac =>
          σ.insert w.address {ac with balance := .ofNat <| ac.balance.toNat + w.amount.toFin.val * 10^9}
