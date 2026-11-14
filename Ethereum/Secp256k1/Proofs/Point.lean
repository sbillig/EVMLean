import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Ethereum.Secp256k1.Proofs.Field

/-!
The point formulas of `Ethereum.Secp256k1.Impl` against Mathlib's Jacobian
coordinates (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian`).

A point `P : Impl.Point` stands for the Jacobian triple `P.coords` over `ZMod p`
and so for the affine point `P.toSpec`. Doubling computes Mathlib's `dblXYZ`
exactly, and addition computes a triple equivalent (a unit multiple) to
Mathlib's `add`. Mathlib proves that `add` is the group law on nonsingular
triples, which gives `toSpec_add`.
-/

namespace Ethereum.Secp256k1.Impl

open Spec WeierstrassCurve WeierstrassCurve.Jacobian

/-- secp256k1 as a curve in Jacobian coordinates. -/
abbrev curveJ : WeierstrassCurve.Jacobian (ZMod p) := curve.toJacobian

/-- The Jacobian coordinates of `P` in `ZMod p`. -/
def Point.coords (P : Point) : Fin 3 → ZMod p := ![P.x, P.y, P.z]

/-- The point of the curve that `P` stands for: `(X / Z², Y / Z³)`, or `0` when `Z = 0`. -/
noncomputable def Point.toSpec (P : Point) : Spec.Point :=
  Jacobian.Point.toAffine curveJ P.coords

/-- `P` stands for a point of the curve. -/
def Point.Valid (P : Point) : Prop := curveJ.Nonsingular P.coords

@[simp] theorem coords_zero (P : Point) : P.coords 0 = P.x := rfl
@[simp] theorem coords_one (P : Point) : P.coords 1 = P.y := rfl
@[simp] theorem coords_two (P : Point) : P.coords 2 = P.z := rfl

@[simp] theorem curve_a₁ : curve.a₁ = 0 := rfl
@[simp] theorem curve_a₂ : curve.a₂ = 0 := rfl
@[simp] theorem curve_a₃ : curve.a₃ = 0 := rfl
@[simp] theorem curve_a₄ : curve.a₄ = 0 := rfl
@[simp] theorem curve_a₆ : curve.a₆ = 7 := rfl

theorem infinity_coords : Point.infinity.coords = ![1, 1, 0] := by
  simp [Point.coords, Point.infinity]

theorem infinity_valid : Point.infinity.Valid := by
  rw [Point.Valid, infinity_coords]
  exact nonsingular_zero

theorem infinity_toSpec : Point.infinity.toSpec = 0 := by
  rw [Point.toSpec, infinity_coords]
  exact Jacobian.Point.toAffine_zero

/-- Doubling computes Mathlib's doubling formula, for every triple. -/
theorem coords_double (P : Point) : P.double.coords = curveJ.dblXYZ P.coords := by
  ext i
  fin_cases i <;>
    simp [Point.double, Point.coords, dblXYZ, dblX, dblY, dblZ, negDblY, dblU_eq, negY] <;>
    ring

theorem double_equiv (P : Point) : P.double.coords ≈ curveJ.add P.coords P.coords := by
  rw [coords_double, add_self]

/-- Addition computes a unit multiple of Mathlib's addition, for nonsingular triples. -/
theorem add_equiv {P Q : Point} (hP : P.Valid) (hQ : Q.Valid) :
    (P.add Q).coords ≈ curveJ.add P.coords Q.coords := by
  unfold Point.Valid at hP hQ
  simp only [Point.add]
  split_ifs with h₁ h₂ hu hs
  · have hPz : P.coords 2 = 0 := natCast_eq_zero_iff_mod.mpr h₁
    by_cases hQz : Q.coords 2 = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz]
      exact Setoid.trans (equiv_of_Z_eq_zero hQ nonsingular_zero hQz rfl)
        (Setoid.symm (smul_equiv _ ((isUnit_X_of_Z_eq_zero hP hPz).pow 2)))
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz]
      exact Setoid.symm (smul_equiv _ ((isUnit_X_of_Z_eq_zero hP hPz).mul (Ne.isUnit hQz)))
  · have hPz : P.coords 2 ≠ 0 := fun h => h₁ (natCast_eq_zero_iff_mod.mp h)
    have hQz : Q.coords 2 = 0 := natCast_eq_zero_iff_mod.mpr h₂
    rw [add_of_Z_eq_zero_right hQ.left hPz hQz]
    exact Setoid.symm
      (smul_equiv _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul (Ne.isUnit hPz)).neg)
  all_goals
    have hPz : P.coords 2 ≠ 0 := fun h => h₁ (natCast_eq_zero_iff_mod.mp h)
    have hQz : Q.coords 2 ≠ 0 := fun h => h₂ (natCast_eq_zero_iff_mod.mp h)
  · have hx : P.coords 0 * Q.coords 2 ^ 2 = Q.coords 0 * P.coords 2 ^ 2 := by
      have := congrArg (fun a : ℕ => (a : ZMod p)) hu
      simp only [natCast_fmul] at this
      simp only [coords_zero, coords_two]
      linear_combination this
    have hy : P.coords 1 * Q.coords 2 ^ 3 = Q.coords 1 * P.coords 2 ^ 3 := by
      have := congrArg (fun a : ℕ => (a : ZMod p)) hs
      simp only [natCast_fmul] at this
      simp only [coords_one, coords_two]
      linear_combination this
    rw [add_of_equiv (equiv_of_X_eq_of_Y_eq hPz hQz hx hy), ← coords_double]
  · have hx : P.coords 0 * Q.coords 2 ^ 2 = Q.coords 0 * P.coords 2 ^ 2 := by
      have := congrArg (fun a : ℕ => (a : ZMod p)) hu
      simp only [natCast_fmul] at this
      simp only [coords_zero, coords_two]
      linear_combination this
    have hy : P.coords 1 * Q.coords 2 ^ 3 ≠ Q.coords 1 * P.coords 2 ^ 3 := by
      intro h
      refine hs ((natCast_inj (fmul_lt _ _) (fmul_lt _ _)).mp ?_)
      simp only [natCast_fmul]
      simp only [coords_one, coords_two] at h
      linear_combination h
    rw [add_of_Y_ne hP.left hQ.left hPz hQz hx hy, infinity_coords]
    exact Setoid.symm (smul_equiv _ (isUnit_addU_of_Y_ne hPz hQz hy))
  · have hx : P.coords 0 * Q.coords 2 ^ 2 ≠ Q.coords 0 * P.coords 2 ^ 2 := by
      intro h
      refine hu ((natCast_inj (fmul_lt _ _) (fmul_lt _ _)).mp ?_)
      simp only [natCast_fmul]
      simp only [coords_zero, coords_two] at h
      linear_combination h
    rw [add_of_not_equiv (not_equiv_of_X_ne hx)]
    convert smul_equiv (curveJ.addXYZ P.coords Q.coords)
      (Ne.isUnit (neg_ne_zero.mpr (mul_ne_zero hPz hQz))) using 1
    rw [smul_fin3]
    have hX := addX_eq' hP.left hQ.left
    have hY := negAddY_eq' (W' := curveJ) P.coords Q.coords
    simp only [addXYZ, addY, negY_eq, addZ, curve_a₁, curve_a₂, curve_a₃, zero_mul, add_zero,
      sub_zero] at hX hY ⊢
    ext i
    fin_cases i <;> simp [Point.coords] at hX hY ⊢
    · linear_combination -hX
    · linear_combination -hY - (P.y * Q.z ^ 3 - Q.y * P.z ^ 3) * hX
    · ring

theorem Point.Valid.double {P : Point} (hP : P.Valid) : P.double.Valid :=
  (nonsingular_of_equiv (double_equiv P)).mpr (nonsingular_add hP hP)

theorem Point.Valid.add {P Q : Point} (hP : P.Valid) (hQ : Q.Valid) : (P.add Q).Valid :=
  (nonsingular_of_equiv (add_equiv hP hQ)).mpr (nonsingular_add hP hQ)

theorem toSpec_double {P : Point} (hP : P.Valid) : P.double.toSpec = P.toSpec + P.toSpec := by
  rw [Point.toSpec, Jacobian.Point.toAffine_of_equiv (double_equiv P),
    Jacobian.Point.toAffine_add hP hP]
  rfl

theorem toSpec_add {P Q : Point} (hP : P.Valid) (hQ : Q.Valid) :
    (P.add Q).toSpec = P.toSpec + Q.toSpec := by
  rw [Point.toSpec, Jacobian.Point.toAffine_of_equiv (add_equiv hP hQ),
    Jacobian.Point.toAffine_add hP hQ]
  rfl

end Ethereum.Secp256k1.Impl
