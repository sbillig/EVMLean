import Ethereum.Weierstrass.Curve
import Ethereum.Secp256k1.Prime
import Ethereum.UInt256
import Ethereum.Wheels

/-!
A specification of secp256k1 public-key recovery and of the ECRECOVER
precompile, in terms of Mathlib's group of points of an elliptic curve.

The curve is `y² = x³ + 7` over `ZMod p`. Mathlib's group law needs `ZMod p` to
be a field, which `p_prime` (a kernel-checked primality certificate) provides.
Recovery follows SEC 1 v2, §4.1.6, for the recovery identifiers `0` and `1`: the
key is `r⁻¹ (s R - e G)`, where `R` is the point with abscissa `r` whose ordinate
has the parity `v`. The scalars `r⁻¹ s` and `r⁻¹ e` are computed in `ZMod n` and
applied to points as natural numbers, so the definition does not depend on `n`
being the order of `G`.
-/

namespace Ethereum.Secp256k1.Spec

instance : Fact p.Prime := ⟨p_prime⟩

instance : NeZero n := ⟨by decide⟩

/-- secp256k1: `y² = x³ + 7` over the integers modulo `p` (SEC 2 v2, §2.4.1). -/
abbrev curve : WeierstrassCurve (ZMod p) := Weierstrass.short p 7

/-- The points of the curve with Mathlib's group law; `0` is the point at infinity. -/
abbrev Point := curve.toAffine.Point

/-- `p` does not divide `0 < k < p`. -/
theorem natCast_ne_zero {k : ℕ} (h0 : 0 < k) (hp : k < p) : (k : ZMod p) ≠ 0 :=
  Weierstrass.natCast_ne_zero h0 hp

/-- On this curve, every solution of the equation is a nonsingular point. -/
theorem nonsingular_iff (x y : ZMod p) : curve.toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 + 7 :=
  Weierstrass.nonsingular_iff (by decide)
    (mod_cast natCast_ne_zero (k := 7) (by norm_num) (by decide)) x y

theorem G_nonsingular : curve.toAffine.Nonsingular (gx : ZMod p) gy := by
  rw [nonsingular_iff]
  have h : ((gy ^ 2 : ℕ) : ZMod p) = ((gx ^ 3 + 7 : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by decide +kernel)
  push_cast at h
  exact h

/-- The generator `G` (SEC 2 v2, §2.4.1). -/
def G : Point := .some _ _ G_nonsingular

open Classical in
/-- The point with abscissa `x` whose ordinate, as a number in `[0, p)`, has the
parity `v`, if there is one. There is at most one, since the two square roots
`y` and `-y ≠ y` of a nonzero number have different parities, `p` being odd. -/
noncomputable def liftX (x : ZMod p) (v : ℕ) : Option Point :=
  if h : ∃ y : ZMod p, curve.toAffine.Nonsingular x y ∧ y.val % 2 = v then
    some (.some _ _ h.choose_spec.1)
  else none

/-- secp256k1 public-key recovery from a message hash `e`, a recovery identifier `v`
and a signature `(r, s)`: the affine coordinates of
`(r⁻¹ s) • R - (r⁻¹ e) • G`, with `R = liftX r v` and the scalars computed modulo
`n`. It is `none` when `r` or `s` is not in `[1, n)`, `v` is not `0` or `1`, no
point has abscissa `r` and parity `v`, or the result is the point at infinity. -/
noncomputable def recover (e v r s : ℕ) : Option (ZMod p × ZMod p) :=
  if 0 < r ∧ r < n ∧ 0 < s ∧ s < n ∧ v < 2 then
    match liftX r v with
    | none => none
    | some R =>
      match (((r : ZMod n)⁻¹ * s).val • R - ((r : ZMod n)⁻¹ * e).val • G : Point) with
      | .zero => none
      | .some x y _ => some (x, y)
  else none

/-- The 64-byte public key `x ‖ y`, each coordinate big-endian. -/
def publicKeyBytes (x y : ZMod p) : ByteArray :=
  Weierstrass.toBytes32 x.val ++ Weierstrass.toBytes32 y.val

/-- The output of the ECRECOVER precompile (address `0x01`) on the call data `d`, when
the call has at least the 3000 gas it costs. The input is read as four 32-byte
big-endian words `h, v, r, s`, padded with zeros. The output is the address of the
recovered key, the last 20 bytes of the Keccak-256 hash of `x ‖ y`, left-padded to 32
bytes; it is empty when `v` is not `27` or `28` or recovery fails. -/
noncomputable def ecrecover (d : ByteArray) : ByteArray :=
  let word (i : ℕ) := fromByteArrayBigEndian (d.readBytes (32 * i) 32)
  let v := word 1
  if v = 27 ∨ v = 28 then
    match recover (word 0) (v - 27) (word 2) (word 3) with
    | some (x, y) => ByteArray.zeroes 12 ++ (KEC (publicKeyBytes x y)).extract 12 32
    | none => .empty
  else .empty

end Ethereum.Secp256k1.Spec
