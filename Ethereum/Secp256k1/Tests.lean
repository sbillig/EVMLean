import Ethereum.Theory.ECRecover

/-!
Test vectors for `Ethereum.Secp256k1.recover` and `ECDSARECOVER`. The checks run
when this module is built (`lake build Ethereum.Secp256k1.Tests`); the library
does not import it.
-/

namespace Ethereum.Secp256k1Tests

open Secp256k1

private def word (n : ℕ) : ByteArray := toBytes32 n

-- go-ethereum's `core/vm/testdata/precompiles/ecRecover.json`, "ValidKey".
private def e₁ := 0x456e9aea5e197a1f1af7a3e85a3212fa4049a3ba34c2289b4c860fc0b0c64ef3
private def r₁ := 0x9242685bf161793cc25603c231bc2f568eb630ea16aa137d2664ac8038825608
private def s₁ := 0x4f8ae3bd7535248d0bd448298cc2e2071e56992d0774dc340c368ae950852ada
private def key₁ : ℕ × ℕ :=
  (0xf57c1d4c961024e998eaec4b6bebec90e788ef5ade22e636ce76111b60db107d,
   0x4c3404b9908a2f357c84ccb48cf412be41d09574a9291c9c7eb5173ccf2a339f)

#guard recover e₁ 1 r₁ s₁ == some key₁

#guard (ECDSARECOVER (word e₁) ⟨#[1]⟩ (word r₁) (word s₁)).toOption.map
    (fun pk => toHex ((KEC pk).extract 12 32)) ==
  some "7156526fbd7a3c72969b54f64e42c10fbb768c8a"

-- The kernel evaluates the implementation on the same vector.
example : recover e₁ 1 r₁ s₁ = some key₁ := by decide +kernel

-- The other parity gives a different key; `s` above `n / 2` is accepted.
#guard recover e₁ 0 r₁ s₁ != some key₁ && (recover e₁ 0 r₁ s₁).isSome
#guard (recover e₁ 0 r₁ (n - s₁)) == some key₁

-- Malformed signatures.
#guard recover e₁ 2 r₁ s₁ == none
#guard recover e₁ 1 0 s₁ == none
#guard recover e₁ 1 n s₁ == none
#guard recover e₁ 1 r₁ 0 == none
#guard recover e₁ 1 r₁ n == none
-- `5³ + 7` is not a square modulo `p`, so no point has abscissa 5.
#guard recover 1 0 5 1 == none
-- `R = k G` with `k = 0x1234567` and `e = 7 k`, `s = 7`: then `s R - e G = 0`.
#guard recover 0x7f6e5d1 0 0xd47644539acec3da5e3ecf5fe8863c628a9c97e8b71e9ea9167a6f4f83c03c32 7 ==
  none

-- ECRECOVER on 128 bytes of call data, and with `v = 29`.
private def env (d : ByteArray) : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }

private def ecrec (v : ℕ) : ByteArray :=
  (Ξ_ECREC default ⟨5000⟩ default (env (word e₁ ++ word v ++ word r₁ ++ word s₁))).2.2.2

#guard toHex (ecrec 28) == "0000000000000000000000007156526fbd7a3c72969b54f64e42c10fbb768c8a"
#guard (ecrec 29).size == 0

end Ethereum.Secp256k1Tests
