import Ethereum.PrecompiledContracts

/-!
The P256VERIFY precompile `Ξ_P256VERIFY` (`0x100`, EIP-7951, from Osaka) in closed form, in terms
of EthLib's `P256Verify.isValid` (the input checks of EIP-7951 and ECDSA verification over
secp256r1, `Secp256r1.verify`).
-/

namespace Ethereum

open EthLib.Execution.Evm.Precompiles.P256Verify

/-- P256VERIFY charges 6,900 gas whenever the gas suffices, and fails only otherwise. Its output
is 1 as a 32-byte word when the call data is 160 bytes holding a valid signature, and empty
otherwise. -/
theorem Ξ_P256VERIFY_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_P256VERIFY σ g A I =
      if g.toNat < 6900 then (∅, ⟨0⟩, A, .empty)
      else (σ, g - .ofNat 6900, A,
        if I.calldata.size = 160 ∧ isValid I.calldata.data.toList = true then VALID
        else .empty) := by
  unfold Ξ_P256VERIFY p256Verify
  simp only [GAS_P256VERIFY, INPUT_BYTES]
  by_cases hg : g.toNat < 6900
  · simp [hg]
  · by_cases hs : I.calldata.size = 160 <;> by_cases hv : isValid I.calldata.data.toList = true <;>
      simp [hg, hs, hv]

/-- `VALID` is 31 zero bytes and a 1. -/
theorem VALID_data : VALID.data = (List.replicate 31 (0 : UInt8) ++ [1]).toArray := rfl

theorem VALID_size : VALID.size = 32 := rfl

/-- The output of P256VERIFY is empty or 32 bytes. -/
theorem Ξ_P256VERIFY_output_size (σ : AccountMap) (g : UInt256) (A : Substate)
    (I : ExecutionEnv) :
    (Ξ_P256VERIFY σ g A I).2.2.2.size = 0 ∨ (Ξ_P256VERIFY σ g A I).2.2.2.size = 32 := by
  rw [Ξ_P256VERIFY_eq]
  split
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

end Ethereum
