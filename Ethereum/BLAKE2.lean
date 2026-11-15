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

/-! ## A fast implementation

`roundsFast` computes the rounds of `F` on the sixteen words of the working vector
held as the scalar fields of one structure, with each round's permutation written out,
so that compiled code updates the words in place without bounds checks or boxing.
`round_eq`, `rounds_eq` and `F_eq_Ffast` prove it equal to the specification, and
the `@[csimp]` lemma `compressInput_eq_fast` makes compiled code run it in place of
the specification. -/

/-- Sixteen words, kept as the scalar fields of one structure: the working vector and
the message block of the fast implementation. -/
structure Words where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  w8 : UInt64
  w9 : UInt64
  w10 : UInt64
  w11 : UInt64
  w12 : UInt64
  w13 : UInt64
  w14 : UInt64
  w15 : UInt64

/-- The words as an array, the representation of the specification. -/
def Words.toArray (s : Words) : Array UInt64 :=
  #[s.w0, s.w1, s.w2, s.w3, s.w4, s.w5, s.w6, s.w7,
    s.w8, s.w9, s.w10, s.w11, s.w12, s.w13, s.w14, s.w15]

/-- Four words, the result of one mixing step. -/
structure Quad where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64

/-- `G` (§ 3.1) on four words `a, b, c, d` and the message words `x, y`. -/
@[inline] def mix (a b c d x y : UInt64) : Quad :=
  let a := a + b + x
  let d := rotr (d ^^^ a) 32
  let c := c + d
  let b := rotr (b ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨a, b, c, d⟩

/-- A round on the working vector `v` with the message words `x₀ … x₁₅` in the order the
round's permutation reads them: `G` on the columns, then on the diagonals. -/
@[inline] def roundWith (v : Words)
    (x₀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ x₁₁ x₁₂ x₁₃ x₁₄ x₁₅ : UInt64) : Words :=
  let c₀ := mix v.w0 v.w4 v.w8 v.w12 x₀ x₁
  let c₁ := mix v.w1 v.w5 v.w9 v.w13 x₂ x₃
  let c₂ := mix v.w2 v.w6 v.w10 v.w14 x₄ x₅
  let c₃ := mix v.w3 v.w7 v.w11 v.w15 x₆ x₇
  let d₀ := mix c₀.a c₁.b c₂.c c₃.d x₈ x₉
  let d₁ := mix c₁.a c₂.b c₃.c c₀.d x₁₀ x₁₁
  let d₂ := mix c₂.a c₃.b c₀.c c₁.d x₁₂ x₁₃
  let d₃ := mix c₃.a c₀.b c₁.c c₂.d x₁₄ x₁₅
  ⟨d₀.a, d₁.a, d₂.a, d₃.a, d₃.b, d₀.b, d₁.b, d₂.b,
   d₂.c, d₃.c, d₀.c, d₁.c, d₁.d, d₂.d, d₃.d, d₀.d⟩

/-- Round `i` of the fast implementation, with the permutation `σ[i mod 10]` written
out. -/
@[inline] def roundFast (m v : Words) (i : Nat) : Words :=
  match i % 10 with
  | 0 => roundWith v m.w0 m.w1 m.w2 m.w3 m.w4 m.w5 m.w6 m.w7
    m.w8 m.w9 m.w10 m.w11 m.w12 m.w13 m.w14 m.w15
  | 1 => roundWith v m.w14 m.w10 m.w4 m.w8 m.w9 m.w15 m.w13 m.w6
    m.w1 m.w12 m.w0 m.w2 m.w11 m.w7 m.w5 m.w3
  | 2 => roundWith v m.w11 m.w8 m.w12 m.w0 m.w5 m.w2 m.w15 m.w13
    m.w10 m.w14 m.w3 m.w6 m.w7 m.w1 m.w9 m.w4
  | 3 => roundWith v m.w7 m.w9 m.w3 m.w1 m.w13 m.w12 m.w11 m.w14
    m.w2 m.w6 m.w5 m.w10 m.w4 m.w0 m.w15 m.w8
  | 4 => roundWith v m.w9 m.w0 m.w5 m.w7 m.w2 m.w4 m.w10 m.w15
    m.w14 m.w1 m.w11 m.w12 m.w6 m.w8 m.w3 m.w13
  | 5 => roundWith v m.w2 m.w12 m.w6 m.w10 m.w0 m.w11 m.w8 m.w3
    m.w4 m.w13 m.w7 m.w5 m.w15 m.w14 m.w1 m.w9
  | 6 => roundWith v m.w12 m.w5 m.w1 m.w15 m.w14 m.w13 m.w4 m.w10
    m.w0 m.w7 m.w6 m.w3 m.w9 m.w2 m.w8 m.w11
  | 7 => roundWith v m.w13 m.w11 m.w7 m.w14 m.w12 m.w1 m.w3 m.w9
    m.w5 m.w0 m.w15 m.w4 m.w8 m.w6 m.w2 m.w10
  | 8 => roundWith v m.w6 m.w15 m.w14 m.w9 m.w11 m.w3 m.w0 m.w8
    m.w12 m.w2 m.w13 m.w7 m.w1 m.w4 m.w10 m.w5
  | _ => roundWith v m.w10 m.w2 m.w8 m.w4 m.w7 m.w6 m.w1 m.w5
    m.w15 m.w11 m.w9 m.w14 m.w3 m.w12 m.w13 m.w0

/-- Rounds `i, i + 1, …, i + k - 1` of the fast implementation. -/
def roundsFast (m : Words) : Nat → Nat → Words → Words
  | 0, _, v => v
  | k + 1, i, v => roundsFast m k (i + 1) (roundFast m v i)

/-- Word `i` of `v`, as the specification reads `v.toArray[i]!`. -/
def Words.get (v : Words) : Nat → UInt64
  | 0 => v.w0
  | 1 => v.w1
  | 2 => v.w2
  | 3 => v.w3
  | 4 => v.w4
  | 5 => v.w5
  | 6 => v.w6
  | 7 => v.w7
  | 8 => v.w8
  | 9 => v.w9
  | 10 => v.w10
  | 11 => v.w11
  | 12 => v.w12
  | 13 => v.w13
  | 14 => v.w14
  | _ => v.w15

/-- `v` with word `i` replaced by `x`, as the specification writes `v.toArray.set! i x`. -/
def Words.set (v : Words) (i : Nat) (x : UInt64) : Words :=
  match i with
  | 0 => { v with w0 := x }
  | 1 => { v with w1 := x }
  | 2 => { v with w2 := x }
  | 3 => { v with w3 := x }
  | 4 => { v with w4 := x }
  | 5 => { v with w5 := x }
  | 6 => { v with w6 := x }
  | 7 => { v with w7 := x }
  | 8 => { v with w8 := x }
  | 9 => { v with w9 := x }
  | 10 => { v with w10 := x }
  | 11 => { v with w11 := x }
  | 12 => { v with w12 := x }
  | 13 => { v with w13 := x }
  | 14 => { v with w14 := x }
  | 15 => { v with w15 := x }
  | _ => v

theorem toArray_get (v : Words) {i : Nat} (h : i < 16) : v.toArray[i]! = v.get i := by
  match i, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | _ + 16, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 16 _))

theorem toArray_set (v : Words) {i : Nat} (h : i < 16) (x : UInt64) :
    v.toArray.set! i x = (v.set i x).toArray := by
  match i, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | 11, _ => rfl
  | 12, _ => rfl
  | 13, _ => rfl
  | 14, _ => rfl
  | 15, _ => rfl
  | _ + 16, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 16 _))

theorem G_eq (v : Words) {a b c d : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16)
    (x y : UInt64) : G v.toArray a b c d x y =
      (let q := mix (v.get a) (v.get b) (v.get c) (v.get d) x y
       ((((v.set a q.a).set b q.b).set c q.c).set d q.d)).toArray := by
  simp only [G, toArray_get v ha, toArray_get v hb, toArray_get v hc, toArray_get v hd,
    toArray_set _ ha, toArray_set _ hb, toArray_set _ hc, toArray_set _ hd]
  rfl

private theorem round_sigma0 (m v : Array UInt64) {i : Nat} (h : i % 10 = 0) :
    round m v i =
      let v := G v 0 4 8 12 m[0]! m[1]!
      let v := G v 1 5 9 13 m[2]! m[3]!
      let v := G v 2 6 10 14 m[4]! m[5]!
      let v := G v 3 7 11 15 m[6]! m[7]!
      let v := G v 0 5 10 15 m[8]! m[9]!
      let v := G v 1 6 11 12 m[10]! m[11]!
      let v := G v 2 7 8 13 m[12]! m[13]!
      G v 3 4 9 14 m[14]! m[15]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma1 (m v : Array UInt64) {i : Nat} (h : i % 10 = 1) :
    round m v i =
      let v := G v 0 4 8 12 m[14]! m[10]!
      let v := G v 1 5 9 13 m[4]! m[8]!
      let v := G v 2 6 10 14 m[9]! m[15]!
      let v := G v 3 7 11 15 m[13]! m[6]!
      let v := G v 0 5 10 15 m[1]! m[12]!
      let v := G v 1 6 11 12 m[0]! m[2]!
      let v := G v 2 7 8 13 m[11]! m[7]!
      G v 3 4 9 14 m[5]! m[3]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma2 (m v : Array UInt64) {i : Nat} (h : i % 10 = 2) :
    round m v i =
      let v := G v 0 4 8 12 m[11]! m[8]!
      let v := G v 1 5 9 13 m[12]! m[0]!
      let v := G v 2 6 10 14 m[5]! m[2]!
      let v := G v 3 7 11 15 m[15]! m[13]!
      let v := G v 0 5 10 15 m[10]! m[14]!
      let v := G v 1 6 11 12 m[3]! m[6]!
      let v := G v 2 7 8 13 m[7]! m[1]!
      G v 3 4 9 14 m[9]! m[4]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma3 (m v : Array UInt64) {i : Nat} (h : i % 10 = 3) :
    round m v i =
      let v := G v 0 4 8 12 m[7]! m[9]!
      let v := G v 1 5 9 13 m[3]! m[1]!
      let v := G v 2 6 10 14 m[13]! m[12]!
      let v := G v 3 7 11 15 m[11]! m[14]!
      let v := G v 0 5 10 15 m[2]! m[6]!
      let v := G v 1 6 11 12 m[5]! m[10]!
      let v := G v 2 7 8 13 m[4]! m[0]!
      G v 3 4 9 14 m[15]! m[8]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma4 (m v : Array UInt64) {i : Nat} (h : i % 10 = 4) :
    round m v i =
      let v := G v 0 4 8 12 m[9]! m[0]!
      let v := G v 1 5 9 13 m[5]! m[7]!
      let v := G v 2 6 10 14 m[2]! m[4]!
      let v := G v 3 7 11 15 m[10]! m[15]!
      let v := G v 0 5 10 15 m[14]! m[1]!
      let v := G v 1 6 11 12 m[11]! m[12]!
      let v := G v 2 7 8 13 m[6]! m[8]!
      G v 3 4 9 14 m[3]! m[13]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma5 (m v : Array UInt64) {i : Nat} (h : i % 10 = 5) :
    round m v i =
      let v := G v 0 4 8 12 m[2]! m[12]!
      let v := G v 1 5 9 13 m[6]! m[10]!
      let v := G v 2 6 10 14 m[0]! m[11]!
      let v := G v 3 7 11 15 m[8]! m[3]!
      let v := G v 0 5 10 15 m[4]! m[13]!
      let v := G v 1 6 11 12 m[7]! m[5]!
      let v := G v 2 7 8 13 m[15]! m[14]!
      G v 3 4 9 14 m[1]! m[9]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma6 (m v : Array UInt64) {i : Nat} (h : i % 10 = 6) :
    round m v i =
      let v := G v 0 4 8 12 m[12]! m[5]!
      let v := G v 1 5 9 13 m[1]! m[15]!
      let v := G v 2 6 10 14 m[14]! m[13]!
      let v := G v 3 7 11 15 m[4]! m[10]!
      let v := G v 0 5 10 15 m[0]! m[7]!
      let v := G v 1 6 11 12 m[6]! m[3]!
      let v := G v 2 7 8 13 m[9]! m[2]!
      G v 3 4 9 14 m[8]! m[11]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma7 (m v : Array UInt64) {i : Nat} (h : i % 10 = 7) :
    round m v i =
      let v := G v 0 4 8 12 m[13]! m[11]!
      let v := G v 1 5 9 13 m[7]! m[14]!
      let v := G v 2 6 10 14 m[12]! m[1]!
      let v := G v 3 7 11 15 m[3]! m[9]!
      let v := G v 0 5 10 15 m[5]! m[0]!
      let v := G v 1 6 11 12 m[15]! m[4]!
      let v := G v 2 7 8 13 m[8]! m[6]!
      G v 3 4 9 14 m[2]! m[10]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma8 (m v : Array UInt64) {i : Nat} (h : i % 10 = 8) :
    round m v i =
      let v := G v 0 4 8 12 m[6]! m[15]!
      let v := G v 1 5 9 13 m[14]! m[9]!
      let v := G v 2 6 10 14 m[11]! m[3]!
      let v := G v 3 7 11 15 m[0]! m[8]!
      let v := G v 0 5 10 15 m[12]! m[2]!
      let v := G v 1 6 11 12 m[13]! m[7]!
      let v := G v 2 7 8 13 m[1]! m[4]!
      G v 3 4 9 14 m[10]! m[5]! := by
  unfold round
  rw [h]
  rfl

private theorem round_sigma9 (m v : Array UInt64) {i : Nat} (h : i % 10 = 9) :
    round m v i =
      let v := G v 0 4 8 12 m[10]! m[2]!
      let v := G v 1 5 9 13 m[8]! m[4]!
      let v := G v 2 6 10 14 m[7]! m[6]!
      let v := G v 3 7 11 15 m[1]! m[5]!
      let v := G v 0 5 10 15 m[15]! m[11]!
      let v := G v 1 6 11 12 m[9]! m[14]!
      let v := G v 2 7 8 13 m[3]! m[12]!
      G v 3 4 9 14 m[13]! m[0]! := by
  unfold round
  rw [h]
  rfl

theorem round_eq (m v : Words) (i : Nat) :
    round m.toArray v.toArray i = (roundFast m v i).toArray := by
  have hi : i % 10 < 10 := Nat.mod_lt _ (by decide)
  unfold roundFast
  generalize hj : i % 10 = j at hi
  match j, hi with
  | 0, _ =>
    rw [round_sigma0 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 1, _ =>
    rw [round_sigma1 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 2, _ =>
    rw [round_sigma2 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 3, _ =>
    rw [round_sigma3 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 4, _ =>
    rw [round_sigma4 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 5, _ =>
    rw [round_sigma5 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 6, _ =>
    rw [round_sigma6 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 7, _ =>
    rw [round_sigma7 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 8, _ =>
    rw [round_sigma8 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | 9, _ =>
    rw [round_sigma9 _ _ hj]
    simp (config := { decide := true }) only [G_eq, toArray_get, Words.get, Words.set]
    rfl
  | _ + 10, h => exact absurd h (Nat.not_lt.mpr (Nat.le_add_left 10 _))

theorem rounds_eq (m : Words) :
    ∀ k i v, rounds m.toArray k i v.toArray = (roundsFast m k i v).toArray
  | 0, _, _ => rfl
  | k + 1, i, v => by
    rw [rounds, round_eq, rounds_eq m k (i + 1)]
    rfl

/-- The words of an array of sixteen. -/
def Words.ofArray (a : Array UInt64) : Words :=
  ⟨a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!, a[8]!, a[9]!, a[10]!, a[11]!,
   a[12]!, a[13]!, a[14]!, a[15]!⟩

theorem ofArray_toArray {a : Array UInt64} (h : a.size = 16) : (Words.ofArray a).toArray = a := by
  obtain ⟨l⟩ := a
  match l, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

/-- `F` with its rounds computed by `roundsFast`. -/
def Ffast (r : Nat) (h m : Array UInt64) (t₀ t₁ : UInt64) (f : Bool) : Array UInt64 :=
  let v := h ++ IV
  let v := (v.set! 12 (v[12]! ^^^ t₀)).set! 13 (v[13]! ^^^ t₁)
  let v := if f then v.set! 14 (~~~v[14]!) else v
  let v := (roundsFast (Words.ofArray m) r 0 (Words.ofArray v)).toArray
  Array.ofFn fun i : Fin 8 => h[i.val]! ^^^ v[i.val]! ^^^ v[i.val + 8]!

theorem F_eq_Ffast (r : Nat) {h m : Array UInt64} (hh : h.size = 8) (hm : m.size = 16)
    (t₀ t₁ : UInt64) (f : Bool) : F r h m t₀ t₁ f = Ffast r h m t₀ t₁ f := by
  have hv : (h ++ IV).size = 16 := by simp [hh, IV]
  unfold F Ffast
  cases f <;>
    simp only [Bool.false_eq_true, ite_true, ite_false] <;>
    rw [← rounds_eq, ofArray_toArray hm, ofArray_toArray (by simp [hv])]

/-- `compressInput`, computed with `Ffast`. -/
def compressInputFast (d : ByteArray) : ByteArray :=
  let r :=
    (d[0]!.toNat <<< 24) ||| (d[1]!.toNat <<< 16) ||| (d[2]!.toNat <<< 8) ||| d[3]!.toNat
  let h := Array.ofFn fun i : Fin 8 => word d (4 + 8 * i.val)
  let m := Array.ofFn fun i : Fin 16 => word d (68 + 8 * i.val)
  let out := Ffast r h m (word d 196) (word d 204) (d[212]! = 1)
  ByteArray.mk <| Array.ofFn fun i : Fin 64 =>
    (out[i.val / 8]! >>> (8 * (i.val % 8)).toUInt64).toUInt8

/-- Compiled code computes `compressInput` as `compressInputFast`. -/
@[csimp] theorem compressInput_eq_fast : @compressInput = @compressInputFast := by
  funext d
  unfold compressInput compressInputFast
  simp only []
  rw [F_eq_Ffast _ Array.size_ofFn Array.size_ofFn]

/-! ## The precompile -/

/-- The output of the BLAKE2 F precompile (EIP-152) on the input `d`: `compressInput d`,
or `none` unless `d` has 213 bytes and a final block flag of 0 or 1. -/
def precompile (d : ByteArray) : Option ByteArray :=
  if d.size = 213 ∧ d[212]! ≤ 1 then some (compressInput d) else none

theorem precompile_eq (d : ByteArray) :
    precompile d = if d.size = 213 ∧ d[212]! ≤ 1 then some (compressInput d) else none := rfl

theorem compressInput_size (d : ByteArray) : (compressInput d).size = 64 := by
  simp only [compressInput, ByteArray.size, Array.size_ofFn]

end Ethereum.BLAKE2
