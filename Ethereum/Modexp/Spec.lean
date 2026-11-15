import Mathlib.Data.Nat.Log
import Ethereum.Wheels

/-!
A specification of the MODEXP precompile (address `0x05`) of EIP-198, priced by EIP-2565
(Berlin to Prague), and from Osaka bounded by EIP-7823 and priced by EIP-7883.

The call data is read as if extended with zero bytes. Its first three 32-byte big-endian words
are the lengths, in bytes, of the base, the exponent and the modulus; the three numbers follow,
each big-endian in that many bytes. The output is `base ^ exponent mod modulus` as a big-endian
number in exactly `modulus_length` bytes: empty for a zero modulus length, and all zero for a
zero modulus. The numbers are natural numbers of any size; in particular the base is not
reduced modulo `2 ^ 256`.
-/

namespace Ethereum.Modexp

/-- The big-endian number of the `w` bytes of `d` from `off`, `d` extended with zeros. -/
def field (d : ByteArray) (off w : ℕ) : ℕ := fromByteArrayBigEndian (d.readWithPadding off w)

/-- The three lengths, in bytes. -/
def baseLength (d : ByteArray) : ℕ := field d 0 32
def expLength (d : ByteArray) : ℕ := field d 32 32
def modLength (d : ByteArray) : ℕ := field d 64 32

/-- The three numbers. -/
def base (d : ByteArray) : ℕ := field d 96 (baseLength d)
def exponent (d : ByteArray) : ℕ := field d (96 + baseLength d) (expLength d)
def modulus (d : ByteArray) : ℕ := field d (96 + baseLength d + expLength d) (modLength d)

/-- The `n`-byte big-endian encoding of `x mod 256 ^ n`. -/
def toBytesBE (n x : ℕ) : ByteArray :=
  ⟨Array.ofFn fun i : Fin n => (x >>> (8 * (n - 1 - i.val))).toUInt8⟩

/-- **EIP-198**: `base ^ exponent mod modulus` in `modulus_length` bytes, zero for a zero
modulus. -/
def output (d : ByteArray) : ByteArray :=
  toBytesBE (modLength d) (if modulus d = 0 then 0 else base d ^ exponent d % modulus d)

/-! ## EIP-2565 pricing -/

/-- `ceil(max(x, y) / 8) ^ 2`. -/
def multiplicationComplexity (x y : ℕ) : ℕ := ((max x y + 7) / 8) ^ 2

/-- The exponent's bit length less one, from its first 32 bytes and its length beyond them. -/
def adjustedExpLength (d : ByteArray) : ℕ :=
  if expLength d ≤ 32 then
    if exponent d = 0 then 0 else Nat.log 2 (exponent d)
  else
    let head := field d (96 + baseLength d) 32
    8 * (expLength d - 32) + if head = 0 then 0 else Nat.log 2 head

/-- **EIP-2565**: `max(200, multiplication_complexity * iteration_count / 3)`. -/
def gas (d : ByteArray) : ℕ :=
  max 200 (multiplicationComplexity (baseLength d) (modLength d) * max (adjustedExpLength d) 1 / 3)

/-! ## Osaka: EIP-7823 bounds and EIP-7883 pricing -/

/-- **EIP-7823** (from Osaka): each of the three lengths is at most 1,024 bytes. A call with a
longer one fails, consuming all the gas. -/
def lengthsBounded (d : ByteArray) : Prop :=
  baseLength d ≤ 1024 ∧ expLength d ≤ 1024 ∧ modLength d ≤ 1024

instance (d : ByteArray) : Decidable (lengthsBounded d) := by
  unfold lengthsBounded; infer_instance

/-- EIP-7883's multiplication complexity: 16 up to 32 bytes, `2 * ceil(max(x, y) / 8) ^ 2`
above. -/
def multiplicationComplexityOsaka (x y : ℕ) : ℕ :=
  if 32 < max x y then 2 * ((max x y + 7) / 8) ^ 2 else 16

/-- EIP-7883's adjusted exponent length: as EIP-2565's, with 16 in place of 8 for each exponent
byte beyond the first 32. -/
def adjustedExpLengthOsaka (d : ByteArray) : ℕ :=
  if expLength d ≤ 32 then
    if exponent d = 0 then 0 else Nat.log 2 (exponent d)
  else
    let head := field d (96 + baseLength d) 32
    16 * (expLength d - 32) + if head = 0 then 0 else Nat.log 2 head

/-- **EIP-7883** (from Osaka): `max(500, multiplication_complexity * iteration_count)`, with no
divisor. -/
def gasOsaka (d : ByteArray) : ℕ :=
  max 500 (multiplicationComplexityOsaka (baseLength d) (modLength d) *
    max (adjustedExpLengthOsaka d) 1)

end Ethereum.Modexp
