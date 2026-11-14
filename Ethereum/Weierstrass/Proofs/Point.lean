import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Ethereum.Weierstrass.Curve
import Ethereum.Weierstrass.Proofs.Field

/-!
The point formulas of `Ethereum.Weierstrass` against Mathlib's Jacobian
coordinates (`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian`), on the curve
`short q b : y² = x³ + b` for a prime `q`.

A point `P : Point` stands for the Jacobian triple `P.coords q` over `ZMod q`
and so for the affine point `P.toSpec q b`. Doubling computes Mathlib's
`dblXYZ` exactly, and addition computes a triple equivalent (a unit multiple)
to Mathlib's `add`. Mathlib proves that `add` is the group law on nonsingular
triples, which gives `toSpec_add`.
-/

namespace Ethereum.Weierstrass

open WeierstrassCurve WeierstrassCurve.Jacobian

variable {q : ℕ} {b : ZMod q}

/-- The Jacobian coordinates of `P` in `ZMod q`. -/
def Point.coords (q : ℕ) (P : Point) : Fin 3 → ZMod q := ![P.x, P.y, P.z]

/-- The point of `y² = x³ + b` that `P` stands for: `(X / Z², Y / Z³)`, or `0` when
`Z = 0`. -/
noncomputable def Point.toSpec [Fact q.Prime] (b : ZMod q) (P : Point) :
    (short q b).toAffine.Point :=
  Jacobian.Point.toAffine (short q b).toJacobian (P.coords q)

/-- `P` stands for a point of `y² = x³ + b`. -/
def Point.Valid (b : ZMod q) (P : Point) : Prop := (short q b).toJacobian.Nonsingular (P.coords q)

@[simp] theorem coords_zero (P : Point) : P.coords q 0 = P.x := rfl
@[simp] theorem coords_one (P : Point) : P.coords q 1 = P.y := rfl
@[simp] theorem coords_two (P : Point) : P.coords q 2 = P.z := rfl

@[simp] theorem short_a₁ : (short q b).a₁ = 0 := rfl
@[simp] theorem short_a₂ : (short q b).a₂ = 0 := rfl
@[simp] theorem short_a₃ : (short q b).a₃ = 0 := rfl
@[simp] theorem short_a₄ : (short q b).a₄ = 0 := rfl
@[simp] theorem short_a₆ : (short q b).a₆ = b := rfl

theorem infinity_coords : Point.infinity.coords q = ![1, 1, 0] := by
  simp [Point.coords, Point.infinity]

theorem infinity_valid [Nontrivial (ZMod q)] : Point.infinity.Valid b := by
  rw [Point.Valid, infinity_coords]
  exact nonsingular_zero

theorem infinity_toSpec [Fact q.Prime] : Point.infinity.toSpec b = 0 := by
  rw [Point.toSpec, infinity_coords]
  exact Jacobian.Point.toAffine_zero

/-- Doubling computes Mathlib's doubling formula, for every triple. -/
theorem coords_double [Fact q.Prime] (P : Point) :
    (P.double q).coords q = (short q b).toJacobian.dblXYZ (P.coords q) := by
  have hq0 := (Fact.out : q.Prime).pos
  ext i
  fin_cases i <;>
    simp [Point.double, Point.coords, dblXYZ, dblX, dblY, dblZ, negDblY, dblU_eq, negY,
      natCast_fsub hq0] <;>
    ring

theorem double_equiv [Fact q.Prime] (P : Point) :
    (P.double q).coords q ≈ (short q b).toJacobian.add (P.coords q) (P.coords q) := by
  rw [coords_double, add_self]

/-- Addition computes a unit multiple of Mathlib's addition, for nonsingular triples. -/
theorem add_equiv [Fact q.Prime] {P Q : Point} (hP : P.Valid b) (hQ : Q.Valid b) :
    (P.add q Q).coords q ≈ (short q b).toJacobian.add (P.coords q) (Q.coords q) := by
  have hq0 := (Fact.out : q.Prime).pos
  unfold Point.Valid at hP hQ
  simp only [Point.add]
  split_ifs with h₁ h₂ hu hs
  · have hPz : P.coords q 2 = 0 := natCast_eq_zero_iff_mod.mpr h₁
    by_cases hQz : Q.coords q 2 = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz]
      exact Setoid.trans (equiv_of_Z_eq_zero hQ nonsingular_zero hQz rfl)
        (Setoid.symm (smul_equiv _ ((isUnit_X_of_Z_eq_zero hP hPz).pow 2)))
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz]
      exact Setoid.symm (smul_equiv _ ((isUnit_X_of_Z_eq_zero hP hPz).mul (Ne.isUnit hQz)))
  · have hPz : P.coords q 2 ≠ 0 := fun h => h₁ (natCast_eq_zero_iff_mod.mp h)
    have hQz : Q.coords q 2 = 0 := natCast_eq_zero_iff_mod.mpr h₂
    rw [add_of_Z_eq_zero_right hQ.left hPz hQz]
    exact Setoid.symm
      (smul_equiv _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul (Ne.isUnit hPz)).neg)
  all_goals
    have hPz : P.coords q 2 ≠ 0 := fun h => h₁ (natCast_eq_zero_iff_mod.mp h)
    have hQz : Q.coords q 2 ≠ 0 := fun h => h₂ (natCast_eq_zero_iff_mod.mp h)
  · have hx : P.coords q 0 * Q.coords q 2 ^ 2 = Q.coords q 0 * P.coords q 2 ^ 2 := by
      have := congrArg (fun a : ℕ => (a : ZMod q)) hu
      simp only [natCast_fmul] at this
      simp only [coords_zero, coords_two]
      linear_combination this
    have hy : P.coords q 1 * Q.coords q 2 ^ 3 = Q.coords q 1 * P.coords q 2 ^ 3 := by
      have := congrArg (fun a : ℕ => (a : ZMod q)) hs
      simp only [natCast_fmul] at this
      simp only [coords_one, coords_two]
      linear_combination this
    rw [add_of_equiv (equiv_of_X_eq_of_Y_eq hPz hQz hx hy), ← coords_double]
  · have hx : P.coords q 0 * Q.coords q 2 ^ 2 = Q.coords q 0 * P.coords q 2 ^ 2 := by
      have := congrArg (fun a : ℕ => (a : ZMod q)) hu
      simp only [natCast_fmul] at this
      simp only [coords_zero, coords_two]
      linear_combination this
    have hy : P.coords q 1 * Q.coords q 2 ^ 3 ≠ Q.coords q 1 * P.coords q 2 ^ 3 := by
      intro h
      refine hs ((natCast_inj (fmul_lt hq0 _ _) (fmul_lt hq0 _ _)).mp ?_)
      simp only [natCast_fmul]
      simp only [coords_one, coords_two] at h
      linear_combination h
    rw [add_of_Y_ne hP.left hQ.left hPz hQz hx hy, infinity_coords]
    exact Setoid.symm (smul_equiv _ (isUnit_addU_of_Y_ne hPz hQz hy))
  · have hx : P.coords q 0 * Q.coords q 2 ^ 2 ≠ Q.coords q 0 * P.coords q 2 ^ 2 := by
      intro h
      refine hu ((natCast_inj (fmul_lt hq0 _ _) (fmul_lt hq0 _ _)).mp ?_)
      simp only [natCast_fmul]
      simp only [coords_zero, coords_two] at h
      linear_combination h
    rw [add_of_not_equiv (not_equiv_of_X_ne hx)]
    convert smul_equiv ((short q b).toJacobian.addXYZ (P.coords q) (Q.coords q))
      (Ne.isUnit (neg_ne_zero.mpr (mul_ne_zero hPz hQz))) using 1
    rw [smul_fin3]
    have hX := addX_eq' hP.left hQ.left
    have hY := negAddY_eq' (W' := (short q b).toJacobian) (P.coords q) (Q.coords q)
    simp only [addXYZ, addY, negY_eq, addZ, short_a₁, short_a₂, short_a₃, zero_mul, add_zero,
      sub_zero] at hX hY ⊢
    ext i
    fin_cases i <;> simp [Point.coords, natCast_fsub hq0] at hX hY ⊢
    · linear_combination -hX
    · linear_combination -hY - (P.y * Q.z ^ 3 - Q.y * P.z ^ 3) * hX
    · ring

theorem Point.Valid.double [Fact q.Prime] {P : Point} (hP : P.Valid b) :
    (P.double q).Valid b :=
  (nonsingular_of_equiv (double_equiv (b := b) P)).mpr (nonsingular_add hP hP)

theorem Point.Valid.add [Fact q.Prime] {P Q : Point} (hP : P.Valid b) (hQ : Q.Valid b) :
    (P.add q Q).Valid b :=
  (nonsingular_of_equiv (add_equiv hP hQ)).mpr (nonsingular_add hP hQ)

theorem toSpec_double [Fact q.Prime] {P : Point} (hP : P.Valid b) :
    (P.double q).toSpec b = P.toSpec b + P.toSpec b := by
  simp only [Point.toSpec]
  rw [Jacobian.Point.toAffine_of_equiv (double_equiv (b := b) P), Jacobian.Point.toAffine_add hP hP]

theorem toSpec_add [Fact q.Prime] {P Q : Point} (hP : P.Valid b) (hQ : Q.Valid b) :
    (P.add q Q).toSpec b = P.toSpec b + Q.toSpec b := by
  simp only [Point.toSpec]
  rw [Jacobian.Point.toAffine_of_equiv (add_equiv hP hQ), Jacobian.Point.toAffine_add hP hQ]

/-! ## Affine points -/

private theorem coords_affine (x y : ℕ) :
    (⟨x, y, 1⟩ : Point).coords q = ![(x : ZMod q), (y : ZMod q), 1] := by
  simp [Point.coords]

/-- An affine point with integer coordinates satisfying the equation. -/
theorem affine_valid [Fact q.Prime] (hq : 3 < q) (hb : b ≠ 0) {x y : ℕ}
    (h : (y : ZMod q) ^ 2 = (x : ZMod q) ^ 3 + b) : (⟨x, y, 1⟩ : Point).Valid b := by
  rw [Point.Valid, coords_affine, nonsingular_some]
  exact (nonsingular_iff hq hb _ _).mpr h

/-- The affine point `(x, y)` with `Z = 1` stands for the curve point `(x, y)`. -/
theorem affine_toSpec [Fact q.Prime] (hq : 3 < q) (hb : b ≠ 0) {x y : ℕ}
    (h : (y : ZMod q) ^ 2 = (x : ZMod q) ^ 3 + b) :
    (⟨x, y, 1⟩ : Point).toSpec b = .some _ _ ((nonsingular_iff hq hb _ _).mpr h) := by
  have hv := affine_valid hq hb h
  rw [Point.Valid, coords_affine] at hv
  rw [Point.toSpec, coords_affine, Jacobian.Point.toAffine_some hv]

/-- `toAffine` returns the reduced coordinates of the point that `P` stands for. -/
theorem toAffine_spec [Fact q.Prime] (hq : 2 < q) {P : Point} (hP : P.Valid b) :
    P.toAffine q = (match P.toSpec b with
      | .zero => none
      | .some x y _ => some (x, y)).map fun c : ZMod q × ZMod q => (c.1.val, c.2.val) := by
  have hq0 : 0 < q := by omega
  unfold Point.toAffine
  split_ifs with hz
  · rw [Point.toSpec, Jacobian.Point.toAffine_of_Z_eq_zero (natCast_eq_zero_iff_mod.mpr hz)]
    rfl
  · have hz' : P.coords q 2 ≠ 0 := fun h => hz (natCast_eq_zero_iff_mod.mp h)
    rw [Point.toSpec, Jacobian.Point.toAffine_of_Z_ne_zero hP hz']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [← ZMod.val_cast_of_lt (fmul_lt hq0 _ _)]
      refine congrArg ZMod.val ?_
      rw [natCast_fmul, natCast_fmul, natCast_finv hq, coords_zero, coords_two]
      ring
    · rw [← ZMod.val_cast_of_lt (fmul_lt hq0 _ _)]
      refine congrArg ZMod.val ?_
      rw [natCast_fmul, natCast_fmul, natCast_fmul, natCast_finv hq, coords_one, coords_two]
      ring

end Ethereum.Weierstrass
