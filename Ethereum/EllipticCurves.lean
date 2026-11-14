-- ECDSASIGN requires the following python packages: coincurve, typing-extensions

import Ethereum.Wheels
import Ethereum.PerformIO
import Conform.Wheels
import Ethereum.SpongeHash.Keccak256
import Ethereum.Secp256k1.Impl

def secp256k1n : ℕ := 115792089237316195423570985008687907852837564279074904382605163141518161494337

def blobSign (e pᵣ : String) : List String :=
  let output := totallySafePerformIO <| IO.Process.run <| pythonCommandOfInput e pᵣ
  let chunks : List String.Slice := (output.split Char.isWhitespace).toList
  chunks.map String.Slice.toString
  where pythonCommandOfInput (e pᵣ : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["Ethereum/EllipticCurvesPy/sign.py", e, pᵣ]
  }

-- Appendix F. Signing Transactions

def ECDSASIGN (e pᵣ : ByteArray) : Except String (ByteArray × ByteArray × ByteArray) := do
  let [r, s, v] := blobSign (toHex e) (toHex pᵣ) | .error "error"
  let v ← ByteArray.ofBlob <| padLeft 2 v -- 2 characters means 1 byte
  let r ← ByteArray.ofBlob <| padLeft 64 r -- 64 characters means 23
  let s ← ByteArray.ofBlob <| padLeft 64 s -- 64 characters means 23
  .ok (v, r, s)

/-- The 64-byte public key `x ‖ y` that signed the hash `e` with signature `(r, s)` and
recovery identifier `v`, each argument read as a big-endian number. It is computed by
`Ethereum.Secp256k1.recover`, and `Ethereum.ECDSARECOVER_eq`
(`Ethereum/Theory/ECRecover.lean`) states it in terms of
`Ethereum.Secp256k1.Spec.recover`. -/
def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  match Ethereum.Secp256k1.recover (Ethereum.fromByteArrayBigEndian e)
      (Ethereum.fromByteArrayBigEndian v) (Ethereum.fromByteArrayBigEndian r)
      (Ethereum.fromByteArrayBigEndian s) with
  | some (x, y) => .ok (Ethereum.Secp256k1.toBytes32 x ++ Ethereum.Secp256k1.toBytes32 y)
  | none => .error "ECDSARECOVER failed"

open Batteries
