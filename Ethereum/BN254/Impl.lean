import Ethereum.Weierstrass.Impl

/-!
Executable addition and scalar multiplication on alt_bn128 (BN254), the curve
`y² = x³ + 3` over the integers modulo `p` of EIP-196, on natural numbers.

Points are decoded from and encoded to pairs of 32-byte big-endian coordinates,
with `(0, 0)` standing for the point at infinity. `Ethereum.BN254.add_eq` and
`Ethereum.BN254.mul_eq` (`Ethereum/BN254/Proofs.lean`) prove that `add` and
`mul` compute `Ethereum.BN254.Spec.add` and `Ethereum.BN254.Spec.mul`.
-/

namespace Ethereum.BN254

open Weierstrass

/-- The field prime of alt_bn128 (EIP-196). -/
def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- The point with coordinates `(x, y)`: the point at infinity for `(0, 0)`, `none` when
a coordinate is not below `p` or `(x, y)` is not on the curve. -/
def decode (x y : Nat) : Option Point :=
  if x < p ∧ y < p then
    if x = 0 ∧ y = 0 then some .infinity
    else if fmul p y y = fadd p (fmul p (fmul p x x) x) 3 then some ⟨x, y, 1⟩ else none
  else none

/-- The 64-byte encoding `x ‖ y` of a point, `(0, 0)` for the point at infinity. -/
def encode (P : Point) : ByteArray :=
  match P.toAffine p with
  | none => toBytes32 0 ++ toBytes32 0
  | some (x, y) => toBytes32 x ++ toBytes32 y

/-- The encoded sum of the points `(x₀, y₀)` and `(x₁, y₁)`, or `none` if one of them
is invalid (the ECADD precompile, EIP-196). -/
def add (x₀ y₀ x₁ y₁ : Nat) : Option ByteArray := do
  let P ← decode x₀ y₀
  let Q ← decode x₁ y₁
  pure (encode (P.add p Q))

/-- The encoded multiple `k • (x, y)`, or `none` if the point is invalid (the ECMUL
precompile, EIP-196). -/
def mul (x y k : Nat) : Option ByteArray := do
  let P ← decode x y
  pure (encode (mulAdd p P .infinity P (k.log2 + 1) k 0))

theorem encode_size (P : Point) : (encode P).size = 64 := by
  unfold encode toBytes32
  split <;> simp [ByteArray.size, Array.size_ofFn]

theorem add_size {x₀ y₀ x₁ y₁ : Nat} {o : ByteArray} (h : add x₀ y₀ x₁ y₁ = some o) :
    o.size = 64 := by
  unfold add at h
  revert h
  cases decode x₀ y₀ <;> cases decode x₁ y₁ <;> intro h <;> cases h
  exact encode_size _

theorem mul_size {x y k : Nat} {o : ByteArray} (h : mul x y k = some o) : o.size = 64 := by
  unfold mul at h
  revert h
  cases decode x y <;> intro h <;> cases h
  exact encode_size _

end Ethereum.BN254
