import Ethereum.PrecompiledContracts

/-!
The pairing check `Ξ_SNARKV` (`0x08`) in terms of EthLib's specification of ECPAIRING: the
decoder `decodePair` and the check `pairingCheck`.

EthLib proves, about these definitions, that `pairingCheck` holds exactly when the product of the
pairings of the pairs is 1, that the pairing is bilinear on the groups of order `q`, and that every
pair `decodePair` accepts is a pair of multiples of the generators (see its `SOUNDNESS.md`,
section alt_bn128). This module uses only the definitions.
-/

namespace Ethereum

open EthLib.Execution.Evm.Precompiles.AltBn128
open EthLib.Cryptography.AltBn128 (pairingCheck)

/-- At Cancun, a pairing check on `n` bytes costs `34000 * (n / 192) + 45000` gas (EIP-1108). -/
theorem ecpairingGas_dencun (n : ℕ) : ecpairingGas .dencun n = 34000 * (n / 192) + 45000 := rfl

/-- The output of ECPAIRING is one 32-byte word. -/
theorem ecpairingWord_size (b : Bool) : (⟨(ecpairingWord b).toArray⟩ : ByteArray).size = 32 := by
  cases b <;> rfl

/-- ECPAIRING charges `34000 k + 45000` gas for `k` whole pairs of 192 bytes. It fails, as when out
of gas, when the gas is short, when the length is not a multiple of 192, or when a pair does not
decode: a coordinate not below the field modulus, a point not on its curve, or a point of `G_2`
outside the group of order `q`. Otherwise it returns the word 1 if the product of the pairings is
1, and the word 0 if not. -/
theorem Ξ_SNARKV_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_SNARKV σ g A I =
      let d := I.calldata
      let gᵣ := 34000 * (d.size / 192) + 45000
      if g.toNat < gᵣ ∨ d.size % 192 ≠ 0 then (∅, ⟨0⟩, A, .empty)
      else
        match (List.range (d.size / 192)).mapM (decodePair d) with
        | .ok pairs => (σ, g - .ofNat gᵣ, A, ⟨(ecpairingWord (pairingCheck pairs)).toArray⟩)
        | .error _ => (∅, ⟨0⟩, A, .empty) := by
  simp only [Ξ_SNARKV, ecpairing, ← ecpairingGas_dencun]
  by_cases hg : g.toNat < ecpairingGas .dencun I.calldata.size
  · simp [hg, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  by_cases hl : I.calldata.size % 192 ≠ 0
  · simp [hg, hl, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  simp only [hg, hl, false_or, ite_false, bind, Except.bind, pure, Except.pure]
  cases (List.range (I.calldata.size / 192)).mapM (decodePair I.calldata) <;> rfl

/-- The empty product is 1. The kernel evaluates the final exponentiation of 1. -/
theorem pairingCheck_nil : pairingCheck [] = true := by decide +kernel

/-- On empty call data, ECPAIRING returns the word 1 for 45000 gas (EIP-197). -/
theorem Ξ_SNARKV_empty (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hd : I.calldata = .empty) (hg : 45000 ≤ g.toNat) :
    Ξ_SNARKV σ g A I = (σ, g - .ofNat 45000, A, ⟨(List.replicate 31 (0 : UInt8) ++ [1]).toArray⟩) := by
  rw [Ξ_SNARKV_eq]
  simp only [hd, ByteArray.size_empty, Nat.zero_div, Nat.mul_zero, Nat.zero_add, Nat.zero_mod]
  rw [ite_eq_right (by omega)]
  simp only [List.range_zero, List.mapM_nil, pure, Except.pure, pairingCheck_nil]
  rfl

end Ethereum
