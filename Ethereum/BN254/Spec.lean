import Ethereum.Weierstrass.Curve
import Ethereum.BN254.Prime
import Ethereum.UInt256
import Ethereum.Wheels

/-!
A specification of the alt_bn128 (BN254) addition and scalar multiplication
precompiles of EIP-196, in terms of Mathlib's group of points of `y² = x³ + 3`
over `ZMod p`.

A point is encoded by two 32-byte big-endian coordinates. Both must be below `p`;
`(0, 0)` encodes the point at infinity, and any other pair must satisfy the curve
equation. EIP-196's G1 is the group of all these points (its order is prime; this
file does not use that). An invalid input makes the precompile fail.
-/

namespace Ethereum.BN254.Spec

open Weierstrass

instance : Fact p.Prime := ⟨p_prime⟩

/-- alt_bn128: `y² = x³ + 3` over the integers modulo `p`. -/
abbrev curve : WeierstrassCurve (ZMod p) := short p 3

/-- The points of the curve with Mathlib's group law; `0` is the point at infinity. -/
abbrev Point := curve.toAffine.Point

open Classical in
/-- The point that the coordinates `(x, y)` encode, if any. -/
noncomputable def decode (x y : ℕ) : Option Point :=
  if x < p ∧ y < p then
    if x = 0 ∧ y = 0 then some 0
    else if h : curve.toAffine.Nonsingular x y then some (.some _ _ h) else none
  else none

/-- The 64-byte encoding `x ‖ y` of a point, `(0, 0)` for the point at infinity. -/
def encode : Point → ByteArray
  | .zero => toBytes32 0 ++ toBytes32 0
  | .some x y _ => toBytes32 x.val ++ toBytes32 y.val

/-- ECADD: the encoded sum of the points encoded by `(x₀, y₀)` and `(x₁, y₁)`, or `none`
if either encoding is invalid. -/
noncomputable def add (x₀ y₀ x₁ y₁ : ℕ) : Option ByteArray := do
  let P ← decode x₀ y₀
  let Q ← decode x₁ y₁
  pure (encode (P + Q))

/-- ECMUL: the encoded multiple `k • P` of the point encoded by `(x, y)`, or `none` if
the encoding is invalid. -/
noncomputable def mul (x y k : ℕ) : Option ByteArray := do
  let P ← decode x y
  pure (encode (k • P))

/-- The `i`-th 32-byte big-endian word of the call data `d`, padded with zeros. -/
def word (d : ByteArray) (i : ℕ) : ℕ := fromByteArrayBigEndian (d.readBytes (32 * i) 32)

end Ethereum.BN254.Spec
