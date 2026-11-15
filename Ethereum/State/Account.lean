import Batteries.Recycling.RBTree
import Ethereum.Maps.StorageMap
import Ethereum.SpongeHash.Keccak256

import Ethereum.UInt256
import Ethereum.Wheels
import Ethereum.State.BlockHeader

namespace Ethereum

/--
  Precompiled contract addresses of a fork.
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}` for Cancun; Osaka adds P256VERIFY at `0x100`
  (EIP-7951).
-/
def π (fork : Fork) : RBTree.RBSet AccountAddress compare :=
  let cancun := (List.range 11).tail.map (Fin.ofNat _)
  RBTree.RBSet.ofList (if fork = .Osaka then cancun ++ [Fin.ofNat _ 0x100] else cancun) compare

inductive ToExecute where
  | Code (code : ByteArray)
  | Precompiled (precompiled : AccountAddress)

structure PersistentAccountState where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : ByteArray
  deriving BEq, Inhabited, Repr

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
-/
structure Account extends PersistentAccountState where
  tstorage : Storage
deriving BEq, Inhabited

def PersistentAccountState.codeHash (self : PersistentAccountState) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (KEC self.code)

def Account.codeHash (self : Account) : UInt256 :=
  self.toPersistentAccountState.codeHash

end Ethereum
