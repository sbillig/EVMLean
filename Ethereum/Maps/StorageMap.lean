/- Storage uses an extensional tree map so equality depends on slot contents. -/

import Std.Data.ExtTreeMap.Lemmas
import Mathlib.Data.Multiset.Sort

import Ethereum.Wheels
import Ethereum.Trie
import Ethereum.SpongeHash.Keccak256


namespace Ethereum

section RemoveLater

abbrev Storage : Type := Std.ExtTreeMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

/-- A slot's entry in the storage trie: the hash of the slot, and the RLP of the value. -/
def Storage.trieEntry (pair : UInt256 × UInt256) : Option (ByteArray × ByteArray) := do
  pure (KEC pair.1.toByteArray, ← RLP (.𝔹 (BE pair.2.toNat)))

def computeTrieRoot (storage : Storage) : Option ByteArray := do
  trieRoot (← storage.toArray.mapM Storage.trieEntry)

end RemoveLater

end Ethereum
