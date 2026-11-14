import Mathlib.FieldTheory.Finite.Basic
import Ethereum.Weierstrass.Lucas

/-!
The arithmetic of `Ethereum.Weierstrass` on natural numbers, cast to `ZMod q`,
is the arithmetic of `ZMod q`.

The lemmas hold for all natural numbers, reduced or not: subtraction reduces
its subtrahend before subtracting it from `a + q`, and the other operations are
ring homomorphisms followed by a reduction.
-/

namespace Ethereum.Weierstrass

/-- Fermat: `a ^ (q - 2)` is the inverse of `a` in `ZMod q`, also for `a = 0`. -/
theorem pow_sub_two_eq_inv {q : ℕ} [Fact q.Prime] (hq : 2 < q) (a : ZMod q) :
    a ^ (q - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · simp [ha, zero_pow (show q - 2 ≠ 0 by omega)]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, show q - 2 + 1 = q - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one ha

theorem natCast_powMod (a b m : ℕ) : ((powMod a b m : ℕ) : ZMod m) = (a : ZMod m) ^ b := by
  rw [powMod_eq, ZMod.natCast_mod, Nat.cast_pow]

variable {q : ℕ}

/-- Reduced numbers are equal exactly when their residues are. -/
theorem natCast_inj {a b : ℕ} (ha : a < q) (hb : b < q) : (a : ZMod q) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem natCast_eq_zero_iff_mod {a : ℕ} : (a : ZMod q) = 0 ↔ a % q = 0 := by
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

@[simp] theorem natCast_fadd (a b : ℕ) : ((fadd q a b : ℕ) : ZMod q) = a + b := by
  simp [fadd, ZMod.natCast_mod]

@[simp] theorem natCast_fsub (hq : 0 < q) (a b : ℕ) :
    ((fsub q a b : ℕ) : ZMod q) = a - b := by
  have h : b % q ≤ a + q := (Nat.mod_lt _ hq).le.trans (Nat.le_add_left _ _)
  rw [fsub, ZMod.natCast_mod, Nat.cast_sub h, Nat.cast_add, ZMod.natCast_self, ZMod.natCast_mod]
  ring

@[simp] theorem natCast_fmul (a b : ℕ) : ((fmul q a b : ℕ) : ZMod q) = a * b := by
  simp [fmul, ZMod.natCast_mod]

@[simp] theorem natCast_finv [Fact q.Prime] (hq : 2 < q) (a : ℕ) :
    ((finv q a : ℕ) : ZMod q) = (a : ZMod q)⁻¹ := by
  rw [finv, natCast_powMod, pow_sub_two_eq_inv hq]

theorem fadd_lt (hq : 0 < q) (a b : ℕ) : fadd q a b < q := Nat.mod_lt _ hq

theorem fsub_lt (hq : 0 < q) (a b : ℕ) : fsub q a b < q := Nat.mod_lt _ hq

theorem fmul_lt (hq : 0 < q) (a b : ℕ) : fmul q a b < q := Nat.mod_lt _ hq

end Ethereum.Weierstrass
