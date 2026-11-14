import Ethereum.UInt256
import Ethereum.BN254.Impl

/-- The output of the ECADD precompile on the coordinates `x₀, y₀, x₁, y₁`, each read as a
big-endian number. `Ethereum.Ξ_BN_ADD_eq` (`Ethereum/Theory/BN254.lean`) states it in
terms of `Ethereum.BN254.Spec.add`. -/
def BN_ADD (x₀ y₀ x₁ y₁ : ByteArray) : Except String ByteArray :=
  match Ethereum.BN254.add (Ethereum.fromByteArrayBigEndian x₀)
      (Ethereum.fromByteArrayBigEndian y₀) (Ethereum.fromByteArrayBigEndian x₁)
      (Ethereum.fromByteArrayBigEndian y₁) with
  | some o => .ok o
  | none => .error "BN_ADD failed"
