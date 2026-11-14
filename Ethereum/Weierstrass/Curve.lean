import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Field.ZMod

/-!
The short Weierstrass curves `y² = x³ + b` over `ZMod q`, as Mathlib's
`WeierstrassCurve`. Mathlib's group law on their points needs `ZMod q` to be a
field, so the lemmas about points assume `Fact q.Prime`.
-/

namespace Ethereum.Weierstrass

/-- The curve `y² = x³ + b` over the integers modulo `q`. -/
def short (q : ℕ) (b : ZMod q) : WeierstrassCurve (ZMod q) :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := b }

/-- `q` does not divide `0 < k < q`. -/
theorem natCast_ne_zero {q k : ℕ} (h0 : 0 < k) (hq : k < q) : (k : ZMod q) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd h0 h) (by omega)

/-- For `q > 3` and `b ≠ 0`, every solution of `y² = x³ + b` is a nonsingular point. -/
theorem nonsingular_iff {q : ℕ} [Fact q.Prime] (hq : 3 < q) {b : ZMod q} (hb : b ≠ 0)
    (x y : ZMod q) : (short q b).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + b := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  simp only [short, zero_mul, add_zero, mul_zero, zero_sub, ne_eq, neg_eq_zero]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  by_contra! hc
  have h3 : (3 : ZMod q) ≠ 0 := mod_cast natCast_ne_zero (k := 3) (by norm_num) hq
  have h2 : (2 : ZMod q) ≠ 0 := mod_cast natCast_ne_zero (k := 2) (by norm_num) (by omega)
  have hx : x = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((mul_eq_zero.mp hc.1).resolve_left h3)
  have hy : y = 0 := (mul_eq_zero.mp hc.2).resolve_left h2
  simp [hx, hy] at h
  exact hb h.symm

end Ethereum.Weierstrass
