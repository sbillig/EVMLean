import Ethereum.PrecompiledContracts

/-!
The BLAKE2 F precompile `Ξ_BLAKE2_F` in terms of `Ethereum.BLAKE2.compressInput`, the
compression function `F` on EIP-152's input format.
-/

namespace Ethereum

/-- The BLAKE2 F precompile charges one gas per round, the rounds being the first four
bytes of the call data `d` read big-endian. It fails, as when out of gas, unless `d` has
213 bytes and a final block flag of 0 or 1, and otherwise returns `compressInput d`. -/
theorem Ξ_BLAKE2_F_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_BLAKE2_F σ g A I =
      let d := I.calldata
      let gᵣ := fromByteArrayBigEndian (d.extract 0 4)
      if g.toNat < gᵣ then (∅, ⟨0⟩, A, .empty)
      else if d.size = 213 ∧ d[212]! ≤ 1 then
        (σ, g - .ofNat gᵣ, A, BLAKE2.compressInput d)
      else (∅, ⟨0⟩, A, .empty) := by
  simp only [Ξ_BLAKE2_F, BLAKE2.precompile_eq, dbgTrace]
  split_ifs <;> rfl

end Ethereum
