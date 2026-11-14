/-!
RIPEMD-160 (H. Dobbertin, A. Bosselaers, B. Preneel, "RIPEMD-160: A Strengthened
Version of RIPEMD", 1996; ISO/IEC 10118-3), transcribed over 32-bit words.

The message is padded as in MD4: a `0x80` byte, zeros up to 56 bytes modulo 64,
and the length in bits as a 64-bit little-endian number. Each 64-byte block is
read as sixteen little-endian words and compressed by two parallel lines of 80
steps each. The digest is the five chaining words, little-endian.

This definition is both the specification and the implementation of the
RIPEMD-160 precompile.
-/

namespace Ethereum.RIPEMD160

/-- The five chaining words. -/
structure State where
  h₀ : UInt32
  h₁ : UInt32
  h₂ : UInt32
  h₃ : UInt32
  h₄ : UInt32

/-- The initial chaining value. -/
def initial : State := ⟨0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0⟩

/-- The nonlinear function of step `j`, from `f₁` (steps 0 to 15) to `f₅`
(steps 64 to 79). -/
def f (j : Nat) (x y z : UInt32) : UInt32 :=
  if j < 16 then x ^^^ y ^^^ z
  else if j < 32 then (x &&& y) ||| (~~~x &&& z)
  else if j < 48 then (x ||| ~~~y) ^^^ z
  else if j < 64 then (x &&& z) ||| (y &&& ~~~z)
  else x ^^^ (y ||| ~~~z)

/-- The added constants of the left line, one per round of 16 steps. -/
def K : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]

/-- The added constants of the right line. -/
def K' : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

/-- The message word read at each step of the left line. -/
def r : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

/-- The message word read at each step of the right line. -/
def r' : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- The left rotation of each step of the left line. -/
def s : Array Nat := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

/-- The left rotation of each step of the right line. -/
def s' : Array Nat := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

/-- Rotation of a word left by `n` bits, for `0 < n < 32`. -/
def rol (x : UInt32) (n : Nat) : UInt32 := (x <<< n.toUInt32) ||| (x >>> (32 - n).toUInt32)

/-- One step: `(A, B, C, D, E)` becomes `(E, T, B, rol₁₀ C, D)` with
`T = rol_s (A + f B C D + X + K) + E`. -/
def step (v : State) (fj x k : UInt32) (sj : Nat) : State :=
  ⟨v.h₄, rol (v.h₀ + fj + x + k) sj + v.h₄, v.h₁, rol v.h₂ 10, v.h₃⟩

/-- The compression function on a block of sixteen words. -/
def compress (h : State) (X : Array UInt32) : State :=
  let (left, right) := (List.range 80).foldl (init := (h, h)) fun (a, b) j =>
    (step a (f j a.h₁ a.h₂ a.h₃) X[r[j]!]! K[j / 16]! s[j]!,
     step b (f (79 - j) b.h₁ b.h₂ b.h₃) X[r'[j]!]! K'[j / 16]! s'[j]!)
  ⟨h.h₁ + left.h₂ + right.h₃, h.h₂ + left.h₃ + right.h₄, h.h₃ + left.h₄ + right.h₀,
   h.h₄ + left.h₀ + right.h₁, h.h₀ + left.h₁ + right.h₂⟩

/-- The message padded to a multiple of 64 bytes. -/
def pad (input : ByteArray) : ByteArray :=
  let zeros := (119 - input.size % 64) % 64
  let bits := 8 * input.size
  input.push 0x80 ++ ByteArray.mk (Array.replicate zeros 0) ++
    ByteArray.mk (Array.ofFn fun i : Fin 8 => (bits >>> (8 * i.val)).toUInt8)

/-- The little-endian word at byte offset `i`. -/
def word (b : ByteArray) (i : Nat) : UInt32 :=
  b[i]!.toUInt32 ||| (b[i + 1]!.toUInt32 <<< 8) ||| (b[i + 2]!.toUInt32 <<< 16) |||
    (b[i + 3]!.toUInt32 <<< 24)

/-- The four little-endian bytes of a word. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- The 20-byte RIPEMD-160 digest. -/
def hash (input : ByteArray) : ByteArray :=
  let m := pad input
  let h := (List.range (m.size / 64)).foldl (init := initial) fun h i =>
    compress h (Array.ofFn fun j : Fin 16 => word m (64 * i + 4 * j.val))
  ⟨(wordBytes h.h₀ ++ wordBytes h.h₁ ++ wordBytes h.h₂ ++ wordBytes h.h₃ ++
    wordBytes h.h₄).toArray⟩

theorem hash_size (input : ByteArray) : (hash input).size = 20 := by
  simp only [hash, wordBytes, ByteArray.size, List.size_toArray, List.length_append,
    List.length_cons, List.length_nil]

end Ethereum.RIPEMD160
