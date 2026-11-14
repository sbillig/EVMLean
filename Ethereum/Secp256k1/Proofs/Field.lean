import Mathlib.FieldTheory.Finite.Basic
import Ethereum.Secp256k1.Spec

/-!
The arithmetic of `Ethereum.Secp256k1.Impl` on natural numbers, cast to
`ZMod p`, is the field arithmetic of `ZMod p`.

The lemmas hold for all natural numbers, reduced or not: subtraction reduces
its subtrahend before subtracting it from `a + p`, and the other operations are
ring homomorphisms followed by a reduction.
-/

namespace Ethereum.Secp256k1

open Spec

instance : Fact n.Prime := ⟨n_prime⟩

theorem two_lt_p : 2 < p := by decide

theorem p_pos : 0 < p := by decide

theorem two_lt_n : 2 < n := by decide

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

/-- Reduced numbers are equal exactly when their residues are. -/
theorem natCast_inj {a b : ℕ} (ha : a < p) (hb : b < p) : (a : ZMod p) = b ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem natCast_eq_zero_iff_mod {a : ℕ} : (a : ZMod p) = 0 ↔ a % p = 0 := by
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

namespace Impl

@[simp] theorem natCast_fadd (a b : ℕ) : ((fadd a b : ℕ) : ZMod p) = a + b := by
  simp [fadd, ZMod.natCast_mod]

@[simp] theorem natCast_fsub (a b : ℕ) : ((fsub a b : ℕ) : ZMod p) = a - b := by
  have h : b % p ≤ a + p := (Nat.mod_lt _ p_pos).le.trans (Nat.le_add_left _ _)
  rw [fsub, ZMod.natCast_mod, Nat.cast_sub h, Nat.cast_add, ZMod.natCast_self, ZMod.natCast_mod]
  ring

@[simp] theorem natCast_fmul (a b : ℕ) : ((fmul a b : ℕ) : ZMod p) = a * b := by
  simp [fmul, ZMod.natCast_mod]

@[simp] theorem natCast_finv (a : ℕ) : ((finv a : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
  rw [finv, natCast_powMod, pow_sub_two_eq_inv two_lt_p]

theorem fadd_lt (a b : ℕ) : fadd a b < p := Nat.mod_lt _ p_pos

theorem fsub_lt (a b : ℕ) : fsub a b < p := Nat.mod_lt _ p_pos

theorem fmul_lt (a b : ℕ) : fmul a b < p := Nat.mod_lt _ p_pos

end Impl

end Ethereum.Secp256k1
