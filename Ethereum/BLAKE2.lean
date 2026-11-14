/-!
The BLAKE2b compression function `F` (RFC 7693, § 3.2) with the number of rounds as
a parameter, and the input and output format of the BLAKE2 F precompile (EIP-152).

`F` mixes the state vector of sixteen 64-bit words with `G` (§ 3.1) in `rounds`
rounds, round `i` using the message permutation `σ[i mod 10]`. BLAKE2b itself uses
12 rounds; EIP-152 takes the count from its input.
-/

namespace Ethereum.BLAKE2

/-- The initialisation vector (§ 2.6). -/
def IV : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- The message word permutations `σ[0] … σ[9]` (§ 2.7). -/
def SIGMA : Array (Array Nat) := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

/-- Rotation of a word right by `n` bits, for `0 < n < 64`. -/
def rotr (x n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- The mixing function `G` (§ 3.1) on the words `a, b, c, d` of `v`, with the message
words `x` and `y`. -/
def G (v : Array UInt64) (a b c d : Nat) (x y : UInt64) : Array UInt64 :=
  let va := v[a]! + v[b]! + x
  let vd := rotr (v[d]! ^^^ va) 32
  let vc := v[c]! + vd
  let vb := rotr (v[b]! ^^^ vc) 24
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 16
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 63
  ((v.set! a va).set! b vb |>.set! c vc).set! d vd

/-- Round `i` of `F` (§ 3.2): `G` on the four columns, then on the four diagonals. -/
def round (m : Array UInt64) (v : Array UInt64) (i : Nat) : Array UInt64 :=
  let s := SIGMA[i % 10]!
  let v := G v 0 4 8 12 m[s[0]!]! m[s[1]!]!
  let v := G v 1 5 9 13 m[s[2]!]! m[s[3]!]!
  let v := G v 2 6 10 14 m[s[4]!]! m[s[5]!]!
  let v := G v 3 7 11 15 m[s[6]!]! m[s[7]!]!
  let v := G v 0 5 10 15 m[s[8]!]! m[s[9]!]!
  let v := G v 1 6 11 12 m[s[10]!]! m[s[11]!]!
  let v := G v 2 7 8 13 m[s[12]!]! m[s[13]!]!
  G v 3 4 9 14 m[s[14]!]! m[s[15]!]!

/-- Rounds `i, i + 1, …, i + k - 1`. -/
def rounds (m : Array UInt64) : Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, v => v
  | k + 1, i, v => rounds m k (i + 1) (round m v i)

/-- The compression function `F` with `r` rounds (§ 3.2), on the state `h` (eight
words), the message block `m` (sixteen words), the offset counter `t₀, t₁` and the
final block flag `f`. -/
def F (r : Nat) (h m : Array UInt64) (t₀ t₁ : UInt64) (f : Bool) : Array UInt64 :=
  let v := h ++ IV
  let v := (v.set! 12 (v[12]! ^^^ t₀)).set! 13 (v[13]! ^^^ t₁)
  let v := if f then v.set! 14 (~~~v[14]!) else v
  let v := rounds m r 0 v
  Array.ofFn fun i : Fin 8 => h[i.val]! ^^^ v[i.val]! ^^^ v[i.val + 8]!

/-- The little-endian word at byte offset `i`. -/
def word (b : ByteArray) (i : Nat) : UInt64 :=
  (List.range 8).foldl (init := 0) fun w j => w ||| (b[i + j]!.toUInt64 <<< (8 * j).toUInt64)

/-- `F` on the 213-byte input format of EIP-152: the rounds as a 4-byte big-endian
number, the state `h` as eight little-endian words, the message `m` as sixteen, the
counter `t` as two, and the final block flag as one byte. The result is the new state as
eight little-endian words. -/
def compressInput (d : ByteArray) : ByteArray :=
  let r :=
    (d[0]!.toNat <<< 24) ||| (d[1]!.toNat <<< 16) ||| (d[2]!.toNat <<< 8) ||| d[3]!.toNat
  let h := Array.ofFn fun i : Fin 8 => word d (4 + 8 * i.val)
  let m := Array.ofFn fun i : Fin 16 => word d (68 + 8 * i.val)
  let out := F r h m (word d 196) (word d 204) (d[212]! = 1)
  ByteArray.mk <| Array.ofFn fun i : Fin 64 =>
    (out[i.val / 8]! >>> (8 * (i.val % 8)).toUInt64).toUInt8

/-- `compressInput` on a valid input. Compiled code runs the C function
`blake2compressb64` of `Ethereum/FFI/ffi.c` instead of this definition, for speed (the
precompile's maximum-rounds test runs 2³² - 1 rounds). That the C function computes
`compressInput` on inputs of 213 bytes with a flag of 0 or 1 is trusted, and
`Ethereum/BLAKE2Tests.lean` and differential tests check it. -/
@[extern "blake2compressb64"]
def compressValid (d : @& { d : ByteArray // d.size = 213 ∧ d[212]! ≤ 1 }) : ByteArray :=
  compressInput d.1

/-- The output of the BLAKE2 F precompile (EIP-152) on the input `d`: `compressInput d`,
or `none` unless `d` has 213 bytes and a final block flag of 0 or 1. -/
def precompile (d : ByteArray) : Option ByteArray :=
  if h : d.size = 213 ∧ d[212]! ≤ 1 then some (compressValid ⟨d, h⟩) else none

theorem precompile_eq (d : ByteArray) :
    precompile d = if d.size = 213 ∧ d[212]! ≤ 1 then some (compressInput d) else none := by
  unfold precompile compressValid
  split <;> simp_all

theorem compressInput_size (d : ByteArray) : (compressInput d).size = 64 := by
  simp only [compressInput, ByteArray.size, Array.size_ofFn]

end Ethereum.BLAKE2
