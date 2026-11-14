import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.Tactic.NormNum.Prime
import Ethereum.Weierstrass.Impl

/-!
Primality certificates checked by the kernel.

`prime_of_lucas` is Lucas's test (`lucas_primality` in Mathlib) with `m - 1`
given as a list of primes whose product it is, and with the powers computed by
`powMod`, which the kernel evaluates on binary numerals. A certificate for a
large prime nests further certificates for the large prime factors of
`m - 1` (a Pratt certificate).
-/

namespace Ethereum.Weierstrass

theorem powModAux_eq (m : ℕ) :
    ∀ fuel a b : ℕ, b < 2 ^ fuel → powModAux m fuel a b = a ^ b % m
  | 0, a, b, hb => by
    obtain rfl : b = 0 := by simpa using hb
    simp [powModAux]
  | fuel + 1, a, b, hb => by
    have ih := powModAux_eq m fuel (a * a % m) (b / 2) (by rw [pow_succ] at hb; omega)
    have hsq : (a * a % m) ^ (b / 2) % m = a ^ (2 * (b / 2)) % m := by
      rw [← Nat.pow_mod, ← pow_two, ← pow_mul]
    simp only [powModAux, ih, hsq]
    split
    · rw [Nat.mul_mod_mod, ← pow_succ']
      congr 2
      omega
    · congr 2
      omega

theorem powMod_eq (a b m : ℕ) : powMod a b m = a ^ b % m :=
  powModAux_eq m _ a b Nat.lt_log2_self

/-- In `ZMod m` with `1 < m`, `a ^ k = 1` exactly when `powMod a k m = 1`. -/
theorem natCast_pow_eq_one_iff {m : ℕ} (hm : 1 < m) (a k : ℕ) :
    (a : ZMod m) ^ k = 1 ↔ powMod a k m = 1 := by
  rw [powMod_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
    Nat.mod_eq_of_lt hm]

/-- Lucas's primality test: `m` is prime when `a` has order `m - 1` modulo `m`. The
order is checked against the prime factors `qs` of `m - 1`, listed with
multiplicity. -/
theorem prime_of_lucas (m a : ℕ) (qs : List ℕ) (hm : 1 < m) (hprod : qs.prod = m - 1)
    (hqs : ∀ q ∈ qs, q.Prime) (ha : powMod a (m - 1) m = 1)
    (hd : ∀ q ∈ qs, powMod a ((m - 1) / q) m ≠ 1) : m.Prime := by
  refine lucas_primality m a ((natCast_pow_eq_one_iff hm _ _).mpr ha) fun q hq hdvd => ?_
  rw [← hprod] at hdvd
  obtain ⟨b, hb, hqb⟩ := (Prime.dvd_prod_iff hq.prime).mp hdvd
  obtain rfl := (Nat.prime_dvd_prime_iff_eq hq (hqs b hb)).mp hqb
  exact fun h => hd q hb ((natCast_pow_eq_one_iff hm _ _).mp h)

/-- Proves `∀ q ∈ qs, q.Prime` for a list of numerals, by the given lemmas for the
large primes and by `norm_num` for the others. -/
macro "prime_factors" "[" ps:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp only [List.forall_mem_cons, List.forall_mem_nil, and_true, true_and, $ps,*]
             <;> norm_num))

end Ethereum.Weierstrass
