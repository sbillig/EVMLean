import Ethereum.UInt256
import Ethereum.BN254.Impl

/-- The output of the ECMUL precompile on the coordinates `x₀, y₀` and the scalar `n`,
each read as a big-endian number. `Ethereum.Ξ_BN_MUL_eq` (`Ethereum/Theory/BN254.lean`)
states it in terms of `Ethereum.BN254.Spec.mul`. -/
def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  match Ethereum.BN254.mul (Ethereum.fromByteArrayBigEndian x₀)
      (Ethereum.fromByteArrayBigEndian y₀) (Ethereum.fromByteArrayBigEndian n) with
  | some o => .ok o
  | none => .error "BN_MUL failed"
