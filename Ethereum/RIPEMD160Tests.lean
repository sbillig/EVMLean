import Ethereum.PrecompiledContracts

/-!
Test vectors for `Ethereum.RIPEMD160.hash` and the RIPEMD-160 precompile. The checks
run when this module is built (`lake build Ethereum.RIPEMD160Tests`); the library does
not import it.
-/

namespace Ethereum.RIPEMD160Tests

private def h (s : String) : String := toHex (RIPEMD160.hash s.toUTF8)

-- The test vectors of the RIPEMD-160 paper (Dobbertin, Bosselaers, Preneel).
#guard h "" == "9c1185a5c5e9fc54612808977ee8f548b2258d31"
#guard h "a" == "0bdc9d2d256b3ee9daae347be6f4dc835a467ffe"
#guard h "abc" == "8eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
#guard h "message digest" == "5d0689ef49d2fae572b881b123a85ffa21595f36"
#guard h "abcdefghijklmnopqrstuvwxyz" == "f71c27109c692c1b56bbdceb5b9d2865b3708dbc"
#guard h "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "12a053384a9c0c88e405a06c27dcf49ada62eb2b"
#guard h "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789" ==
  "b0e20b6e3116640286ed3a87a5713079b21f5189"
#guard h (String.join (List.replicate 8 "1234567890")) ==
  "9b752e45573d4b39f4dbd3323cab82bf63326bfb"

-- The precompile left-pads the digest to 32 bytes and charges 600 + 120 per word.
private def env (d : ByteArray) : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }

#guard toHex (Ξ_RIP160 default ⟨1000⟩ default (env "abc".toUTF8)).2.2.2 ==
  "0000000000000000000000008eb208f7e05d987a9b044a8e98c6b087f15a0bfc"
#guard (Ξ_RIP160 default ⟨1000⟩ default (env "abc".toUTF8)).2.1 == ⟨1000 - 720⟩

-- The kernel evaluates the hash.
example : RIPEMD160.hash "abc".toUTF8 = ⟨#[0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b,
    0x04, 0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc]⟩ := by
  decide +kernel

end Ethereum.RIPEMD160Tests
