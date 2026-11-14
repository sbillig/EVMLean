import Ethereum.PrecompiledContracts
import Ethereum.BN254.Proofs

/-!
The alt_bn128 precompiles `Ξ_BN_ADD` and `Ξ_BN_MUL` in terms of the specifications
`Ethereum.BN254.Spec.add` and `Ethereum.BN254.Spec.mul`.
-/

namespace Ethereum

open BN254

/-- ECADD charges 150 gas and returns `Spec.add` of the four words of its call data. On
an invalid point it fails as when out of gas: the account map is empty and no gas is
left. -/
theorem Ξ_BN_ADD_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_BN_ADD σ g A I =
      if g.toNat < 150 then (∅, ⟨0⟩, A, .empty)
      else
        let d := I.calldata
        match Spec.add (Spec.word d 0) (Spec.word d 1) (Spec.word d 2) (Spec.word d 3) with
        | some o => (σ, g - .ofNat 150, A, o)
        | none => (∅, ⟨0⟩, A, .empty) := by
  by_cases hg : g.toNat < 150
  · simp only [Ξ_BN_ADD, if_pos hg]
  simp only [Ξ_BN_ADD, if_neg hg, BN_ADD, Spec.word, ← add_eq, Nat.mul_zero, Nat.mul_one,
    show 32 * 2 = 64 from rfl, show 32 * 3 = 96 from rfl]
  rcases BN254.add (fromByteArrayBigEndian (I.calldata.readBytes 0 32))
    (fromByteArrayBigEndian (I.calldata.readBytes 32 32))
    (fromByteArrayBigEndian (I.calldata.readBytes 64 32))
    (fromByteArrayBigEndian (I.calldata.readBytes 96 32)) with _ | o <;> simp [dbgTrace]

/-- ECMUL charges 6000 gas and returns `Spec.mul` of the three words of its call data. On
an invalid point it fails as when out of gas. -/
theorem Ξ_BN_MUL_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_BN_MUL σ g A I =
      if g.toNat < 6000 then (∅, ⟨0⟩, A, .empty)
      else
        let d := I.calldata
        match Spec.mul (Spec.word d 0) (Spec.word d 1) (Spec.word d 2) with
        | some o => (σ, g - .ofNat 6000, A, o)
        | none => (∅, ⟨0⟩, A, .empty) := by
  by_cases hg : g.toNat < 6000
  · simp only [Ξ_BN_MUL, if_pos hg]
  simp only [Ξ_BN_MUL, if_neg hg, BN_MUL, Spec.word, ← mul_eq, Nat.mul_zero, Nat.mul_one,
    show 32 * 2 = 64 from rfl]
  rcases BN254.mul (fromByteArrayBigEndian (I.calldata.readBytes 0 32))
    (fromByteArrayBigEndian (I.calldata.readBytes 32 32))
    (fromByteArrayBigEndian (I.calldata.readBytes 64 32)) with _ | o <;> simp [dbgTrace]

end Ethereum
