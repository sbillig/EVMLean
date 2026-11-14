import Ethereum.Weierstrass.Proofs.Point

/-!
`mulAdd` computes `a • P + b • Q` in Mathlib's group of points, for scalars below
`2 ^ k`, by induction on `k`.
-/

namespace Ethereum.Weierstrass

variable {q : ℕ} [Fact q.Prime] {b : ZMod q}

private theorem nsmul_halves (c : ℕ) (X : (short q b).toAffine.Point) :
    c • X = (c / 2) • X + (c / 2) • X + (c % 2) • X := by
  rw [← add_nsmul, ← add_nsmul]
  congr 1
  omega

theorem mulAdd_spec {P Q PQ : Point} (hP : P.Valid b) (hQ : Q.Valid b) (hPQ : PQ.Valid b)
    (hsum : PQ.toSpec b = P.toSpec b + Q.toSpec b) :
    ∀ k m l, m < 2 ^ k → l < 2 ^ k →
      (mulAdd q P Q PQ k m l).Valid b ∧
        (mulAdd q P Q PQ k m l).toSpec b = m • P.toSpec b + l • Q.toSpec b
  | 0, m, l, hm, hl => by
    obtain rfl : m = 0 := by simpa using hm
    obtain rfl : l = 0 := by simpa using hl
    exact ⟨infinity_valid, by simp [mulAdd, infinity_toSpec]⟩
  | k + 1, m, l, hm, hl => by
    rw [pow_succ] at hm hl
    obtain ⟨hv, ht⟩ := mulAdd_spec hP hQ hPQ hsum k (m / 2) (l / 2) (by omega) (by omega)
    have hd := toSpec_double hv
    rw [ht] at hd
    rw [nsmul_halves m, nsmul_halves l]
    simp only [mulAdd]
    split_ifs with h₁ h₂ h₂
    · refine ⟨hv.double.add hPQ, ?_⟩
      rw [toSpec_add hv.double hPQ, hd, hsum, h₁, h₂, one_nsmul, one_nsmul]
      abel
    · refine ⟨hv.double.add hP, ?_⟩
      rw [toSpec_add hv.double hP, hd, h₁, show l % 2 = 0 by omega, one_nsmul, zero_nsmul]
      abel
    · refine ⟨hv.double.add hQ, ?_⟩
      rw [toSpec_add hv.double hQ, hd, h₂, show m % 2 = 0 by omega, one_nsmul, zero_nsmul]
      abel
    · refine ⟨hv.double, ?_⟩
      rw [hd, show m % 2 = 0 by omega, show l % 2 = 0 by omega, zero_nsmul, zero_nsmul]
      abel

end Ethereum.Weierstrass
