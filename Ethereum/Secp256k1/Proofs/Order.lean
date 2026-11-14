import Ethereum.Secp256k1.Proofs.Recover
import Ethereum.Weierstrass.Order
import Ethereum.Weierstrass.Cube

/-!
The group of points of secp256k1 has prime order `n` (`card_point`): `n • G = 0` (`nsmul_G`)
and `G ≠ 0`, the group has at most `2 p + 1 < 3 n` points, and `x³ + 7` has no root modulo `p`
(`cube_add_seven_ne_zero`), so `card_eq` of `Weierstrass/Order.lean` applies. So the group is
cyclic, `n` kills every point, every point is a multiple of `G`, and the scalar of a multiple
counts modulo `n`.
-/

namespace Ethereum.Secp256k1

open Spec Weierstrass WeierstrassCurve

/-- `-7` is not a cube modulo `p`: its `(p - 1) / 3`-th power is not one. -/
theorem neg_seven_pow_ne_one : powMod (p - 7) ((p - 1) / 3) p ≠ 1 := by
  decide +kernel

/-- `x³ + 7` has no root modulo `p`: no point of secp256k1 has order two. -/
theorem cube_add_seven_ne_zero (x : ZMod p) : x ^ 3 + 7 ≠ 0 := by
  simpa using cube_add_ne_zero (c := 7) (by decide) (by decide) (by decide) neg_seven_pow_ne_one x

theorem G_ne_zero : G ≠ 0 := Affine.Point.some_ne_zero G_nonsingular

theorem seven_ne_zero : (7 : ZMod p) ≠ 0 :=
  mod_cast Spec.natCast_ne_zero (k := 7) (by norm_num) (by decide)

/-- **The order**: secp256k1 has `n` points. -/
theorem card_point : Nat.card Spec.Point = n :=
  card_eq (by decide) seven_ne_zero cube_add_seven_ne_zero n_prime (by decide) G_ne_zero nsmul_G

/-- The group is cyclic. -/
theorem isAddCyclic_point : IsAddCyclic Spec.Point := isAddCyclic_of_card n_prime card_point

/-- `n` kills every point. -/
theorem nsmul_n (P : Spec.Point) : n • P = 0 := nsmul_card card_point P

/-- The scalar of a multiple counts modulo `n`. -/
theorem mod_n_nsmul (k : ℕ) (P : Spec.Point) : (k % n) • P = k • P := mod_nsmul card_point k P

/-- Every point is a multiple of `G`. -/
theorem exists_nsmul_G (P : Spec.Point) : ∃ k < n, k • G = P :=
  exists_nsmul_eq n_prime card_point G_ne_zero P

end Ethereum.Secp256k1
