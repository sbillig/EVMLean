import Ethereum.PrecompiledContracts
import Ethereum.Secp256k1.Proofs.Recover

/-!
`ECDSARECOVER` and the ECRECOVER precompile `Ξ_ECREC` in terms of the
specification of secp256k1 public-key recovery, `Ethereum.Secp256k1.Spec.recover`,
and of the precompile's output, `Ethereum.Secp256k1.Spec.ecrecover`.
-/

namespace Ethereum

open Secp256k1

/-- `ECDSARECOVER` returns the encoding of the key that `Spec.recover` specifies. -/
theorem ECDSARECOVER_eq (e v r s : ByteArray) :
    ECDSARECOVER e v r s =
      match Spec.recover (fromByteArrayBigEndian e) (fromByteArrayBigEndian v)
          (fromByteArrayBigEndian r) (fromByteArrayBigEndian s) with
      | some (x, y) => .ok (Spec.publicKeyBytes x y)
      | none => .error "ECDSARECOVER failed" := by
  unfold ECDSARECOVER
  rw [recover_eq]
  cases Spec.recover _ _ _ _ <;> rfl

private theorem fromByteArrayBigEndian_recoveryId {v : ℕ} (hv : v = 27 ∨ v = 28) :
    fromByteArrayBigEndian ⟨#[.ofNat v - 27]⟩ = v - 27 := by
  rcases hv with rfl | rfl <;> decide +kernel

private theorem secp256k1n_eq : secp256k1n = n := rfl

/-- The ECRECOVER precompile charges 3000 gas and returns `Spec.ecrecover` of its call
data. -/
theorem Ξ_ECREC_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Ξ_ECREC σ g A I =
      if g.toNat < 3000 then (∅, ⟨0⟩, A, .empty)
      else (σ, g - .ofNat 3000, A, Spec.ecrecover I.calldata) := by
  by_cases hg : g.toNat < 3000
  · simp only [Ξ_ECREC, if_pos hg]
  simp only [Ξ_ECREC, if_neg hg, Prod.mk.injEq, true_and, Spec.ecrecover, Nat.mul_zero,
    Nat.mul_one, show 32 * 2 = 64 from rfl, show 32 * 3 = 96 from rfl, secp256k1n_eq]
  generalize fromByteArrayBigEndian (I.calldata.readBytes 32 32) = v
  by_cases hv : v = 27 ∨ v = 28
  · rw [if_pos hv]
    split_ifs with hguard
    · -- The precompile rejects `r` or `s` out of range, as `Spec.recover` does.
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hguard
      unfold Spec.recover
      rw [if_neg (by omega)]
    · rw [ECDSARECOVER_eq, fromByteArrayBigEndian_recoveryId hv]
      rcases Spec.recover (fromByteArrayBigEndian (I.calldata.readBytes 0 32)) (v - 27)
        (fromByteArrayBigEndian (I.calldata.readBytes 64 32))
        (fromByteArrayBigEndian (I.calldata.readBytes 96 32)) with _ | ⟨x, y⟩
      · simp [dbgTrace]
      · rfl
  · rw [if_neg hv, if_pos]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega

end Ethereum
