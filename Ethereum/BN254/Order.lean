import Ethereum.BN254.Proofs
import Ethereum.BN254.PrimeR
import Ethereum.Weierstrass.Order
import Ethereum.Weierstrass.Cube

/-!
The group of points of alt_bn128 (BN254) has prime order `r` (`card_point`), and the
endomorphism `(x, y) ↦ (β x, y)` that fevm's GLV multiplication uses is multiplication by `λ`
(`endo_eq_nsmul`).

* `cube_add_three_ne_zero`: `x³ + 3` has no root modulo `p`, so no point has order two.
* `nsmul_G`: the generator `G = (1, 2)` has `r • G = 0`, by evaluating `r • G` with `mulAdd` in
  the kernel; `G ≠ 0`, so `G` has order `r`, and `card_eq` of `Weierstrass/Order.lean` gives
  the order of the group: `r` divides it, and it is at most `2 p + 1 < 3 r`, and not `2 r`.
* So the group is cyclic, `r` kills every point, every point is a multiple of `G`, and the
  scalar of a multiple counts modulo `r` (`nsmul_r`, `exists_nsmul_G`, `mod_r_nsmul`).
* `β` (`BETA` of fevm's `bn254.fe`) is a cube root of unity modulo `p`, and `λ` (`LAMBDA`, the
  root of `λ² + λ + 1` modulo `r` that fevm's lattice constants `GLV_A1`, `GLV_B1`, `GLV_A2`,
  `GLV_B2` are a basis for) is the one that goes with it: `(β x, y) = λ • (x, y)` holds at `G`
  by computation, so for every point, the endomorphism being additive and `G` generating.
-/

namespace Ethereum.BN254

open Spec Weierstrass WeierstrassCurve

theorem three_lt_p' : 3 < p := by decide

theorem three_ne_zero' : (3 : ZMod p) ≠ 0 :=
  mod_cast natCast_ne_zero (k := 3) (by norm_num) three_lt_p'

/-- `-3` is not a cube modulo `p`: its `(p - 1) / 3`-th power is not one. -/
theorem neg_three_pow_ne_one : powMod (p - 3) ((p - 1) / 3) p ≠ 1 := by
  decide +kernel

/-- `x³ + 3` has no root modulo `p`: no point of alt_bn128 has order two. -/
theorem cube_add_three_ne_zero (x : ZMod p) : x ^ 3 + 3 ≠ 0 := by
  simpa using cube_add_ne_zero (c := 3) (by decide) (by decide) (by decide) neg_three_pow_ne_one x

/-! ## The order -/

theorem G_nonsingular : curve.toAffine.Nonsingular 1 2 := by
  rw [nonsingular_iff three_lt_p' three_ne_zero']; norm_num

/-- The generator `(1, 2)` of EIP-196. -/
noncomputable def G : Spec.Point := .some 1 2 G_nonsingular

theorem G_ne_zero : G ≠ 0 := Affine.Point.some_ne_zero G_nonsingular

private theorem G_sq : ((2 : ℕ) : ZMod p) ^ 2 = ((1 : ℕ) : ZMod p) ^ 3 + 3 := by norm_num

theorem G_toSpec : (⟨1, 2, 1⟩ : Weierstrass.Point).toSpec (3 : ZMod p) = G := by
  rw [affine_toSpec three_lt_p' three_ne_zero' G_sq, G, Affine.Point.some.injEq]
  norm_num

/-- `r • G = 0`, by evaluating `r • G` with `mulAdd` in the kernel. -/
theorem nsmul_G : r • G = 0 := by
  have hG := affine_valid three_lt_p' three_ne_zero' G_sq
  obtain ⟨-, h⟩ := mulAdd_spec hG infinity_valid hG
    (by rw [infinity_toSpec, add_zero]) 256 r 0 (by decide) (by decide)
  have hz : (mulAdd p ⟨1, 2, 1⟩ .infinity ⟨1, 2, 1⟩ 256 r 0).z % p = 0 := by
    decide +kernel
  generalize mulAdd p ⟨1, 2, 1⟩ .infinity ⟨1, 2, 1⟩ 256 r 0 = Q at h hz
  have hQz : Q.coords p 2 = 0 := natCast_eq_zero_iff_mod.mpr hz
  rw [infinity_toSpec, zero_nsmul, add_zero, G_toSpec, Weierstrass.Point.toSpec,
    Jacobian.Point.toAffine_of_Z_eq_zero hQz] at h
  exact h.symm

/-- **The order**: alt_bn128 has `r` points. -/
theorem card_point : Nat.card Spec.Point = r :=
  card_eq three_lt_p' three_ne_zero' cube_add_three_ne_zero r_prime (by decide) G_ne_zero nsmul_G

/-- The group is cyclic. -/
theorem isAddCyclic_point : IsAddCyclic Spec.Point := isAddCyclic_of_card r_prime card_point

/-- `r` kills every point. -/
theorem nsmul_r (P : Spec.Point) : r • P = 0 := nsmul_card card_point P

/-- The scalar of a multiple counts modulo `r`. -/
theorem mod_r_nsmul (k : ℕ) (P : Spec.Point) : (k % r) • P = k • P := mod_nsmul card_point k P

/-- Every point is a multiple of `G`. -/
theorem exists_nsmul_G (P : Spec.Point) : ∃ k < r, k • G = P :=
  exists_nsmul_eq r_prime card_point G_ne_zero P

/-! ## The endomorphism -/

/-- fevm's `BETA`: a primitive cube root of unity modulo `p`. -/
def BETA : ℕ := 0x59e26bcea0d48bacd4f263f1acdb5c4f5763473177fffffe

/-- The root of `λ² + λ + 1` modulo `r` for which `(β x, y) = λ • (x, y)`. -/
def LAMBDA : ℕ := 0xb3c4d79d41a917585bfc41088d8daaa78b17ea66b99c90dd

/-- fevm's lattice constants: `(GLV_A1, -GLV_B1)` and `(GLV_A2, GLV_B2)` are vectors `(u, v)`
with `u + v λ ≡ 0 (mod r)`. -/
def GLV_A1 : ℕ := 0x89d3256894d213e3
def GLV_B1 : ℕ := 0x6f4d8248eeb859fc8211bbeb7d4f1128
def GLV_A2 : ℕ := 0x6f4d8248eeb859fd0be4e1541221250b
def GLV_B2 : ℕ := 0x89d3256894d213e3

theorem beta_cube : (BETA : ZMod p) ^ 3 = 1 :=
  (natCast_pow_eq_one_iff (by decide) _ _).mpr (by decide +kernel)

theorem beta_ne_one : (BETA : ZMod p) ≠ 1 := by
  rw [← Nat.cast_one, ne_eq, ZMod.natCast_eq_natCast_iff']
  decide

theorem lambda_root : ((LAMBDA : ℕ) : ZMod r) ^ 2 + LAMBDA + 1 = 0 := by
  rw [← Nat.cast_pow, ← Nat.cast_add, ← Nat.cast_one, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  decide +kernel

theorem glv_1 : ((GLV_A1 : ℕ) : ZMod r) = GLV_B1 * LAMBDA := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff']
  decide +kernel

theorem glv_2 : ((GLV_A2 : ℕ) : ZMod r) + GLV_B2 * LAMBDA = 0 := by
  rw [← Nat.cast_mul, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  decide +kernel

/-- `(x, y) ↦ (β x, y)`. -/
noncomputable def endo : Spec.Point →+ Spec.Point := phiHom three_lt_p' three_ne_zero' beta_cube

theorem endo_some {x y : ZMod p} (h : curve.toAffine.Nonsingular x y) :
    endo (.some x y h) = .some (BETA * x) y (phi_nonsingular three_lt_p' three_ne_zero' beta_cube h) :=
  rfl

/-- `λ • G = (β, 2)`, by evaluating `λ • G` with `mulAdd` in the kernel. -/
theorem endo_G : endo G = LAMBDA • G := by
  have hG := affine_valid three_lt_p' three_ne_zero' G_sq
  obtain ⟨hv, h⟩ := mulAdd_spec hG infinity_valid hG
    (by rw [infinity_toSpec, add_zero]) 256 LAMBDA 0 (by decide) (by decide)
  have ha : (mulAdd p ⟨1, 2, 1⟩ .infinity ⟨1, 2, 1⟩ 256 LAMBDA 0).toAffine p = some (BETA, 2) := by
    decide +kernel
  have hs := toAffine_spec (by decide) hv
  rw [ha] at hs
  rw [infinity_toSpec, nsmul_zero, add_zero, G_toSpec] at h
  rw [← h]
  revert hs
  rcases (mulAdd p ⟨1, 2, 1⟩ .infinity ⟨1, 2, 1⟩ 256 LAMBDA 0).toSpec (3 : ZMod p) with _ | ⟨x, y, hxy⟩
  · intro hs; simp at hs
  · intro hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    rw [G, endo_some, Affine.Point.some.injEq]
    constructor
    · rw [mul_one, hs.1, ZMod.natCast_zmod_val]
    · rw [← ZMod.natCast_zmod_val y, ← hs.2]; rfl

/-- **The endomorphism is multiplication by `λ`**: `(β x, y) = λ • (x, y)` for every point. -/
theorem endo_eq_nsmul (P : Spec.Point) : endo P = LAMBDA • P :=
  phi_eq_nsmul three_lt_p' three_ne_zero' beta_cube r_prime card_point G_ne_zero endo_G P

end Ethereum.BN254
