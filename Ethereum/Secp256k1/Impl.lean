import Ethereum.Weierstrass.Impl

/-!
Executable secp256k1 public-key recovery on natural numbers, with the
curve-generic arithmetic of `Ethereum/Weierstrass/Impl.lean` for `y² = x³ + 7`
modulo `p`. The scalar multiplication works in Jacobian coordinates and needs
one field inversion, at the end.
`Ethereum.Secp256k1.recover_eq` (`Ethereum/Secp256k1/Proofs/Recover.lean`)
proves that `recover` computes `Ethereum.Secp256k1.Spec.recover`.

Every function recurses structurally, so the kernel can evaluate them.
-/

namespace Ethereum.Secp256k1

open Weierstrass

/-- The field prime of secp256k1, `2²⁵⁶ - 2³² - 977` (SEC 2 v2, §2.4.1). -/
def p : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- The order of the generator of secp256k1 (SEC 2 v2, §2.4.1). -/
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- The abscissa of the generator (SEC 2 v2, §2.4.1). -/
def gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798

/-- The ordinate of the generator (SEC 2 v2, §2.4.1). -/
def gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

namespace Impl

/-- The point with abscissa `x < p` whose ordinate is a square root of `x³ + 7` of
parity `v`, if there is one. The candidate root is `(x³ + 7) ^ ((p + 1) / 4)`, since
`p ≡ 3 (mod 4)`, or its negative. -/
def liftX (x v : Nat) : Option Point :=
  let α := fadd p (fmul p (fmul p x x) x) 7
  let β := powMod α ((p + 1) / 4) p
  let y := if β % 2 = v then β else (p - β) % p
  if fmul p y y = α ∧ y % 2 = v then some ⟨x, y, 1⟩ else none

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
      let negG : Point := ⟨gx, p - gy, 1⟩
      (mulAdd p R negG (R.add p negG) 256 u₂ u₁).toAffine p
  else none

end Ethereum.Secp256k1
