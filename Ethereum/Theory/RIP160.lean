import Ethereum.PrecompiledContracts

/-!
The RIPEMD-160 precompile `Ξ_RIP160` in terms of `Ethereum.RIPEMD160.hash`.
-/

namespace Ethereum

/-- The RIPEMD-160 precompile charges `600 + 120 ⌈l / 32⌉` gas for `l` bytes of call data
and returns their digest, left-padded with zeros to 32 bytes. -/
theorem Ξ_RIP160_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_RIP160 σ g A I =
      let gᵣ := 600 + 120 * ((I.calldata.size + 31) / 32)
      if g.toNat < gᵣ then (∅, ⟨0⟩, A, .empty)
      else (σ, g - .ofNat gᵣ, A, ByteArray.zeroes 12 ++ RIPEMD160.hash I.calldata) := by
  simp only [Ξ_RIP160, RIP160]

end Ethereum
