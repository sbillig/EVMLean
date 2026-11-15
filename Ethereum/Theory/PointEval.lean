import Ethereum.PrecompiledContracts

/-!
The point evaluation precompile `Ξ_PointEval` (`0x0a`) in terms of EthLib's specification of
EIP-4844: the versioned hash `kzgCommitmentToVersionedHash` and the KZG check `verifyKzgProof`.

EthLib checks the length of the call data before the gas. `Ξ_PointEval_eq` shows that the order is
not visible through `Ξ`: both failures consume all the gas, and the theorem states the two
conditions as one disjunction.
-/

namespace Ethereum

open EthLib.Execution.Evm.Precompiles.PointEvaluation
open EthLib.Cryptography.Kzg (kzgCommitmentToVersionedHash)
open EthLib.Base (readBytes)

/-- The output of every successful call: 4096 (`FIELD_ELEMENTS_PER_BLOB`) and `BLS_MODULUS`, as
two 32-byte big-endian words. -/
theorem output_data :
    output.data.toList =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       0x10, 0x00,
       0x73, 0xed, 0xa7, 0x53, 0x29, 0x9d, 0x7d, 0x48, 0x33, 0x39, 0xd8, 0x08, 0x09, 0xa1, 0xd8, 0x05,
       0x53, 0xbd, 0xa4, 0x02, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x01] := by
  decide +kernel

theorem output_size : output.size = 64 := by
  rw [ByteArray.size, ← Array.length_toList, output_data]
  rfl

/-- Point evaluation charges 50000 gas. It fails, as when out of gas, when the gas is short or the
call data is not 192 bytes, when the versioned hash (bytes 0 to 31) is not the one of the
commitment (bytes 96 to 143), or when the proof (bytes 144 to 191) does not show that the
commitment's polynomial takes the value `y` (bytes 64 to 95) at `z` (bytes 32 to 63). Otherwise it
returns `output`. -/
theorem Ξ_PointEval_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_PointEval σ g A I =
      let d := I.calldata
      if h : g.toNat < 50000 ∨ d.size ≠ 192 then (∅, ⟨0⟩, A, .empty)
      else
        let commitment := readBytes d 96 48 (by omega)
        if kzgCommitmentToVersionedHash commitment = readBytes d 0 32 (by omega) ∧
            verifyKzgProof commitment (readBytes d 32 32 (by omega)) (readBytes d 64 32 (by omega))
              (readBytes d 144 48 (by omega)) = .ok true
        then (σ, g - .ofNat 50000, A, output)
        else (∅, ⟨0⟩, A, .empty) := by
  simp only [Ξ_PointEval, pointEvaluation, INPUT_BYTES, GAS_POINT_EVALUATION]
  by_cases hl : I.calldata.size = 192
  · rw [dite_eq_left hl]
    by_cases hg : g.toNat < 50000
    · simp [hg, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [dite_eq_right (by omega)]
    simp only [hg, ite_false, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure,
      Except.pure]
    by_cases hh : kzgCommitmentToVersionedHash (readBytes I.calldata 96 48 (by omega)) =
        readBytes I.calldata 0 32 (by omega)
    · simp only [hh, ne_eq, not_true_eq_false, ite_false, true_and]
      cases verifyKzgProof (readBytes I.calldata 96 48 (by omega))
          (readBytes I.calldata 32 32 (by omega)) (readBytes I.calldata 64 32 (by omega))
          (readBytes I.calldata 144 48 (by omega)) with
      | error e => simp
      | ok b => cases b <;> simp
    · simp [hh]
  · rw [dite_eq_right hl, dite_eq_left (Or.inr hl)]

end Ethereum
