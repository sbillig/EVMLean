import Ethereum.Weierstrass.Curve
import Ethereum.Weierstrass.Lucas
import Mathlib.FieldTheory.Finite.Basic

/-!
`x³ + c` without a root modulo a prime `q ≡ 1 (mod 3)`: a root would make `-c` a cube, so
`(-c) ^ ((q - 1) / 3) = x ^ (q - 1) = 1`; a `powMod` the kernel evaluates shows it is not
one (`cube_add_ne_zero`). Such a curve `y² = x³ + c` has no point with `y = 0`, that is no
point of order two.
-/

namespace Ethereum.Weierstrass

theorem cube_add_ne_zero {q : ℕ} [Fact q.Prime] {c : ℕ} (hc0 : 0 < c) (hcq : c < q)
    (h3 : 3 * ((q - 1) / 3) = q - 1) (h : powMod (q - c) ((q - 1) / 3) q ≠ 1) (x : ZMod q) :
    x ^ 3 + c ≠ 0 := by
  intro hx3
  have hx : x ≠ 0 := by
    rintro rfl
    exact natCast_ne_zero hc0 hcq (by simpa using hx3)
  have hc : x ^ 3 = ((q - c : ℕ) : ZMod q) := by
    rw [Nat.cast_sub hcq.le, ZMod.natCast_self, zero_sub]
    linear_combination hx3
  apply h
  rw [← natCast_pow_eq_one_iff (Fact.out : q.Prime).one_lt, ← hc, ← pow_mul, h3,
    ZMod.pow_card_sub_one_eq_one hx]

end Ethereum.Weierstrass
