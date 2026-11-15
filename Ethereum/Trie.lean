import EthLib.Execution.Trie.Root
import Ethereum.SpongeHash.Keccak256

/-!
Roots of Merkle Patricia tries: `TRIE` of the Yellow Paper (Appendix D), computed by EthLib's
`EthLib.Execution.Trie.root` with Keccak-256.
-/

namespace Ethereum

/-- `KEC` as the 32-byte vector that EthLib's trie hashes with. -/
def KEC₃₂ (b : ByteArray) : EthLib.Base.Hash32 := ⟨(KEC b).data, Keccak256.hash_size_eq_32 b⟩

/--
`TRIE` of the key-value pairs: the hash of the root node's encoding. Each key is the path itself;
for the state and storage tries it is already the Keccak-256 hash of the address or slot. The
keys are distinct at every call site. `none` when a value is empty, which the trie cannot hold
and no caller gives.
-/
def trieRoot (kvs : Array (ByteArray × ByteArray)) : Option ByteArray :=
  (EthLib.Execution.Trie.root KEC₃₂ ⟨false, kvs.toList⟩).toOption.map (⟨·.toArray⟩)

end Ethereum
