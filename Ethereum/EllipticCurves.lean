import Ethereum.Wheels
import Ethereum.SpongeHash.Keccak256
import Ethereum.Secp256k1.Impl

def secp256k1n : ℕ := 115792089237316195423570985008687907852837564279074904382605163141518161494337

/-- The 64-byte public key `x ‖ y` that signed the hash `e` with signature `(r, s)` and
recovery identifier `v`, each argument read as a big-endian number. It is computed by
`Ethereum.Secp256k1.recover`, and `Ethereum.ECDSARECOVER_eq`
(`Ethereum/Theory/ECRecover.lean`) states it in terms of
`Ethereum.Secp256k1.Spec.recover`. -/
def ECDSARECOVER (e v r s : ByteArray) : Except String ByteArray :=
  match Ethereum.Secp256k1.recover (Ethereum.fromByteArrayBigEndian e)
      (Ethereum.fromByteArrayBigEndian v) (Ethereum.fromByteArrayBigEndian r)
      (Ethereum.fromByteArrayBigEndian s) with
  | some (x, y) => .ok (Ethereum.Weierstrass.toBytes32 x ++ Ethereum.Weierstrass.toBytes32 y)
  | none => .error "ECDSARECOVER failed"

open Batteries
