/-!
Executable arithmetic on the short Weierstrass curves `y² = x³ + b` over the
integers modulo a prime `q`, on natural numbers.

Field elements are natural numbers, reduced modulo `q` by every operation.
Points are kept in Jacobian coordinates `(X, Y, Z)`, which stand for the affine
point `(X / Z², Y / Z³)` when `Z ≠ 0` and for the point at infinity when `Z = 0`.
The doubling and addition formulas do not involve `b`.
`Ethereum/Weierstrass/Proofs` relates them to Mathlib's group of points.

Every function recurses structurally, so the kernel can evaluate them.
-/

namespace Ethereum.Weierstrass

/-- `a ^ b % m` by square and multiply on the low `fuel` bits of `b`. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 1 % m
  | fuel + 1, a, b =>
    let h := powModAux m fuel (a * a % m) (b / 2)
    if b % 2 = 1 then a * h % m else h

/-- `a ^ b % m`. -/
def powMod (a b m : Nat) : Nat := powModAux m (b.log2 + 1) a b

/-- The 32-byte big-endian encoding of `x mod 2²⁵⁶`. -/
def toBytes32 (x : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 32 => (x >>> (8 * (31 - i.val))).toUInt8⟩

/-! ## Arithmetic modulo `q` -/

/-- `a + b` modulo `q`. -/
@[inline] def fadd (q a b : Nat) : Nat := (a + b) % q

/-- `a - b` modulo `q`. -/
@[inline] def fsub (q a b : Nat) : Nat := (a + q - b % q) % q

/-- `a * b` modulo `q`. -/
@[inline] def fmul (q a b : Nat) : Nat := a * b % q

/-- `a⁻¹` modulo a prime `q`, as `a ^ (q - 2)` (Fermat); `0` for `a ≡ 0`. -/
def finv (q a : Nat) : Nat := powMod a (q - 2) q

/-! ## Points in Jacobian coordinates -/

/-- A point in Jacobian coordinates. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat

/-- The point at infinity. -/
def Point.infinity : Point := ⟨1, 1, 0⟩

/-- `2 • P` for a curve `y² = x³ + b` (the formulas of `dbl-2009-l` for `a = 0`). -/
def Point.double (q : Nat) (P : Point) : Point :=
  let xx := fmul q P.x P.x
  let yy := fmul q P.y P.y
  let yyyy := fmul q yy yy
  let s := fmul q 4 (fmul q P.x yy)
  let m := fmul q 3 xx
  let x₃ := fsub q (fmul q m m) (fmul q 2 s)
  ⟨x₃, fsub q (fmul q m (fsub q s x₃)) (fmul q 8 yyyy), fmul q 2 (fmul q P.y P.z)⟩

/-- `P + Q`, for all `P` and `Q` (the formulas of `add-1998-cmo-2`, with the cases
`P = 0`, `Q = 0`, `P = Q` and `P = -Q` handled separately). -/
def Point.add (q : Nat) (P Q : Point) : Point :=
  if P.z % q = 0 then Q
  else if Q.z % q = 0 then P
  else
    let z₁z₁ := fmul q P.z P.z
    let z₂z₂ := fmul q Q.z Q.z
    let u₁ := fmul q P.x z₂z₂
    let u₂ := fmul q Q.x z₁z₁
    let s₁ := fmul q P.y (fmul q Q.z z₂z₂)
    let s₂ := fmul q Q.y (fmul q P.z z₁z₁)
    if u₁ = u₂ then
      if s₁ = s₂ then P.double q else .infinity
    else
      let h := fsub q u₂ u₁
      let r := fsub q s₂ s₁
      let hh := fmul q h h
      let hhh := fmul q h hh
      let v := fmul q u₁ hh
      let x₃ := fsub q (fsub q (fmul q r r) hhh) (fmul q 2 v)
      ⟨x₃, fsub q (fmul q r (fsub q v x₃)) (fmul q s₁ hhh), fmul q (fmul q P.z Q.z) h⟩

/-- `a • P + b • Q` for `a, b < 2 ^ k`, given `PQ = P + Q`, by one doubling per bit
from the highest (Shamir's trick). -/
def mulAdd (q : Nat) (P Q PQ : Point) : Nat → Nat → Nat → Point
  | 0, _, _ => .infinity
  | k + 1, a, b =>
    let t := (mulAdd q P Q PQ k (a / 2) (b / 2)).double q
    if a % 2 = 1 then
      if b % 2 = 1 then t.add q PQ else t.add q P
    else
      if b % 2 = 1 then t.add q Q else t

/-- The affine coordinates of a point, or `none` for the point at infinity. -/
def Point.toAffine (q : Nat) (P : Point) : Option (Nat × Nat) :=
  if P.z % q = 0 then none
  else
    let zi := finv q P.z
    let zi2 := fmul q zi zi
    some (fmul q P.x zi2, fmul q P.y (fmul q zi zi2))

end Ethereum.Weierstrass
