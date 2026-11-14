/-!
Executable secp256k1 public-key recovery on natural numbers.

Field elements are natural numbers reduced modulo `p`. Points are kept in
Jacobian coordinates `(X, Y, Z)`, which stand for the affine point
`(X / Z², Y / Z³)` when `Z ≠ 0` and for the point at infinity when `Z = 0`, so
the scalar multiplication needs one field inversion, at the end.
`Ethereum.Secp256k1.recover_eq` (`Ethereum/Secp256k1/Proofs/Recover.lean`)
proves that `recover` computes `Ethereum.Secp256k1.Spec.recover`.

Every function recurses structurally, so the kernel can evaluate them.
-/

namespace Ethereum.Secp256k1

/-- The field prime of secp256k1, `2²⁵⁶ - 2³² - 977` (SEC 2 v2, §2.4.1). -/
def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- The order of the generator of secp256k1 (SEC 2 v2, §2.4.1). -/
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- The abscissa of the generator (SEC 2 v2, §2.4.1). -/
def gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- The ordinate of the generator (SEC 2 v2, §2.4.1). -/
def gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

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

namespace Impl

/-! ## Arithmetic modulo `p` -/

/-- `a + b` modulo `p`. -/
@[inline] def fadd (a b : Nat) : Nat := (a + b) % p

/-- `a - b` modulo `p`. -/
@[inline] def fsub (a b : Nat) : Nat := (a + p - b % p) % p

/-- `a * b` modulo `p`. -/
@[inline] def fmul (a b : Nat) : Nat := a * b % p

/-- `a⁻¹` modulo `p`, as `a ^ (p - 2)` (Fermat); `0` for `a ≡ 0`. -/
def finv (a : Nat) : Nat := powMod a (p - 2) p

/-! ## Points in Jacobian coordinates -/

/-- A point in Jacobian coordinates. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat

/-- The point at infinity. -/
def Point.infinity : Point := ⟨1, 1, 0⟩

/-- `2 • P` for the curve `y² = x³ + 7` (the formulas of `dbl-2009-l` for `a = 0`). -/
def Point.double (P : Point) : Point :=
  let xx := fmul P.x P.x
  let yy := fmul P.y P.y
  let yyyy := fmul yy yy
  let s := fmul 4 (fmul P.x yy)
  let m := fmul 3 xx
  let x₃ := fsub (fmul m m) (fmul 2 s)
  ⟨x₃, fsub (fmul m (fsub s x₃)) (fmul 8 yyyy), fmul 2 (fmul P.y P.z)⟩

/-- `P + Q`, for all `P` and `Q` (the formulas of `add-1998-cmo-2`, with the cases
`P = 0`, `Q = 0`, `P = Q` and `P = -Q` handled separately). -/
def Point.add (P Q : Point) : Point :=
  if P.z % p = 0 then Q
  else if Q.z % p = 0 then P
  else
    let z₁z₁ := fmul P.z P.z
    let z₂z₂ := fmul Q.z Q.z
    let u₁ := fmul P.x z₂z₂
    let u₂ := fmul Q.x z₁z₁
    let s₁ := fmul P.y (fmul Q.z z₂z₂)
    let s₂ := fmul Q.y (fmul P.z z₁z₁)
    if u₁ = u₂ then
      if s₁ = s₂ then P.double else infinity
    else
      let h := fsub u₂ u₁
      let r := fsub s₂ s₁
      let hh := fmul h h
      let hhh := fmul h hh
      let v := fmul u₁ hh
      let x₃ := fsub (fsub (fmul r r) hhh) (fmul 2 v)
      ⟨x₃, fsub (fmul r (fsub v x₃)) (fmul s₁ hhh), fmul (fmul P.z Q.z) h⟩

/-- `a • P + b • Q` for `a, b < 2 ^ k`, given `PQ = P + Q`, by one doubling per bit
from the highest (Shamir's trick). -/
def mulAdd (P Q PQ : Point) : Nat → Nat → Nat → Point
  | 0, _, _ => .infinity
  | k + 1, a, b =>
    let t := (mulAdd P Q PQ k (a / 2) (b / 2)).double
    if a % 2 = 1 then
      if b % 2 = 1 then t.add PQ else t.add P
    else
      if b % 2 = 1 then t.add Q else t

/-- The affine coordinates of a point, or `none` for the point at infinity. -/
def Point.toAffine (P : Point) : Option (Nat × Nat) :=
  if P.z % p = 0 then none
  else
    let zi := finv P.z
    let zi2 := fmul zi zi
    some (fmul P.x zi2, fmul P.y (fmul zi zi2))

/-- The point with abscissa `x < p` whose ordinate is a square root of `x³ + 7` of
parity `v`, if there is one. The candidate root is `(x³ + 7) ^ ((p + 1) / 4)`, since
`p ≡ 3 (mod 4)`, or its negative. -/
def liftX (x v : Nat) : Option Point :=
  let α := fadd (fmul (fmul x x) x) 7
  let β := powMod α ((p + 1) / 4) p
  let y := if β % 2 = v then β else (p - β) % p
  if fmul y y = α ∧ y % 2 = v then some ⟨x, y, 1⟩ else none

end Impl

/-- Public-key recovery: the affine coordinates of `r⁻¹ (s R - e G)`, where `R` is the
point with abscissa `r` and ordinate of parity `v`, and the inverse and the products
of scalars are taken modulo `n`; `none` when `r` or `s` is not in `[1, n)`, `v` is not
`0` or `1`, no such `R` exists, or the result is the point at infinity. -/
def recover (e v r s : Nat) : Option (Nat × Nat) :=
  if 0 < r ∧ r < n ∧ 0 < s ∧ s < n ∧ v < 2 then
    match Impl.liftX r v with
    | none => none
    | some R =>
      let rinv := powMod r (n - 2) n
      let u₁ := rinv * e % n
      let u₂ := rinv * s % n
      let negG : Impl.Point := ⟨gx, p - gy, 1⟩
      (Impl.mulAdd R negG (R.add negG) 256 u₂ u₁).toAffine
  else none

end Ethereum.Secp256k1
