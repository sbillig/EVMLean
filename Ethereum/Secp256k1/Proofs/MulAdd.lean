import Ethereum.Secp256k1.Proofs.Point

/-!
`Impl.mulAdd` computes `a • P + b • Q` in Mathlib's group of points, for
scalars below `2 ^ k`, by induction on `k`.
-/

namespace Ethereum.Secp256k1.Impl

open Spec

private theorem nsmul_halves (c : ℕ) (X : Spec.Point) :
    c • X = (c / 2) • X + (c / 2) • X + (c % 2) • X := by
  rw [← add_nsmul, ← add_nsmul]
  congr 1
  omega

theorem mulAdd_spec {P Q PQ : Point} (hP : P.Valid) (hQ : Q.Valid) (hPQ : PQ.Valid)
    (hsum : PQ.toSpec = P.toSpec + Q.toSpec) :
    ∀ k a b, a < 2 ^ k → b < 2 ^ k →
      (mulAdd P Q PQ k a b).Valid ∧
        (mulAdd P Q PQ k a b).toSpec = a • P.toSpec + b • Q.toSpec
  | 0, a, b, ha, hb => by
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : b = 0 := by simpa using hb
    exact ⟨infinity_valid, by simp [mulAdd, infinity_toSpec]⟩
  | k + 1, a, b, ha, hb => by
    rw [pow_succ] at ha hb
    obtain ⟨hv, ht⟩ := mulAdd_spec hP hQ hPQ hsum k (a / 2) (b / 2) (by omega) (by omega)
    have hd := toSpec_double hv
    rw [ht] at hd
    rw [nsmul_halves a, nsmul_halves b]
    simp only [mulAdd]
    split_ifs with h₁ h₂ h₂
    · refine ⟨hv.double.add hPQ, ?_⟩
      rw [toSpec_add hv.double hPQ, hd, hsum, h₁, h₂, one_nsmul, one_nsmul]
      abel
    · refine ⟨hv.double.add hP, ?_⟩
      rw [toSpec_add hv.double hP, hd, h₁, show b % 2 = 0 by omega, one_nsmul, zero_nsmul]
      abel
    · refine ⟨hv.double.add hQ, ?_⟩
      rw [toSpec_add hv.double hQ, hd, h₂, show a % 2 = 0 by omega, one_nsmul, zero_nsmul]
      abel
    · refine ⟨hv.double, ?_⟩
      rw [hd, show a % 2 = 0 by omega, show b % 2 = 0 by omega, zero_nsmul, zero_nsmul]
      abel

end Ethereum.Secp256k1.Impl
