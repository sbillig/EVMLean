/-!
SHA-256 (FIPS 180-4, §§ 4.1.2, 4.2.2, 5.1.1, 5.3.3 and 6.2), transcribed over
32-bit words.

The message is padded with a `0x80` byte, zeros up to 56 bytes modulo 64, and the
length in bits as a 64-bit big-endian number. Each 64-byte block is read as
sixteen big-endian words, expanded to the 64-word message schedule and compressed
by 64 rounds. The digest is the eight chaining words, big-endian.

This definition is both the specification and the implementation of the SHA-256
precompile.
-/

namespace Ethereum.SHA256

/-- The round constants `K₀ … K₆₃` (§ 4.2.2). -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- The initial hash value `H⁽⁰⁾` (§ 5.3.3). -/
def initial : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Rotation of a word right by `n` bits, for `0 < n < 32`. -/
def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bigSigma₀ (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bigSigma₁ (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def smallSigma₀ (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def smallSigma₁ (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The message schedule `W₀ … W₆₃` of a block of sixteen words (§ 6.2.2, step 1). -/
def schedule (M : Array UInt32) : Array UInt32 :=
  (List.range 48).foldl (init := M) fun W i =>
    let t := i + 16
    W.push (smallSigma₁ W[t - 2]! + W[t - 7]! + smallSigma₀ W[t - 15]! + W[t - 16]!)

/-- One round: `(a, …, h)` becomes `(T₁ + T₂, a, b, c, d + T₁, e, f, g)`. -/
def round (v : Array UInt32) (k w : UInt32) : Array UInt32 :=
  let T₁ := v[7]! + bigSigma₁ v[4]! + ch v[4]! v[5]! v[6]! + k + w
  let T₂ := bigSigma₀ v[0]! + maj v[0]! v[1]! v[2]!
  #[T₁ + T₂, v[0]!, v[1]!, v[2]!, v[3]! + T₁, v[4]!, v[5]!, v[6]!]

/-- The compression of one block of sixteen words into the hash value `H` (§ 6.2.2). -/
def compress (H M : Array UInt32) : Array UInt32 :=
  let W := schedule M
  let v := (List.range 64).foldl (init := H) fun v t => round v K[t]! W[t]!
  Array.ofFn fun i : Fin 8 => H[i.val]! + v[i.val]!

/-- The message padded to a multiple of 64 bytes (§ 5.1.1). -/
def pad (input : ByteArray) : ByteArray :=
  let zeros := (119 - input.size % 64) % 64
  let bits := 8 * input.size
  input.push 0x80 ++ ByteArray.mk (Array.replicate zeros 0) ++
    ByteArray.mk (Array.ofFn fun i : Fin 8 => (bits >>> (8 * (7 - i.val))).toUInt8)

/-- The big-endian word at byte offset `i`. -/
def word (b : ByteArray) (i : Nat) : UInt32 :=
  (b[i]!.toUInt32 <<< 24) ||| (b[i + 1]!.toUInt32 <<< 16) ||| (b[i + 2]!.toUInt32 <<< 8) |||
    b[i + 3]!.toUInt32

/-- The 32-byte SHA-256 digest. -/
def hash (input : ByteArray) : ByteArray :=
  let m := pad input
  let H := (List.range (m.size / 64)).foldl (init := initial) fun H i =>
    compress H (Array.ofFn fun j : Fin 16 => word m (64 * i + 4 * j.val))
  ByteArray.mk <| Array.ofFn fun i : Fin 32 =>
    (H[i.val / 4]! >>> (8 * (3 - i.val % 4)).toUInt32).toUInt8

theorem hash_size (input : ByteArray) : (hash input).size = 32 := by
  simp only [hash, ByteArray.size, Array.size_ofFn]

end Ethereum.SHA256
