import Ethereum.PrecompiledContracts

/-!
The SHA-256 precompile `Ξ_SHA256` in terms of `Ethereum.SHA256.hash`.
-/

namespace Ethereum

/-- The SHA-256 precompile charges `60 + 12 ⌈l / 32⌉` gas for `l` bytes of call data and
returns their digest. -/
theorem Ξ_SHA256_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_SHA256 σ g A I =
      let gᵣ := 60 + 12 * ((I.calldata.size + 31) / 32)
      if g.toNat < gᵣ then (∅, ⟨0⟩, A, .empty)
      else (σ, g - .ofNat gᵣ, A, SHA256.hash I.calldata) := by
  simp only [Ξ_SHA256]

end Ethereum
