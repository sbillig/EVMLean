import Ethereum.PrecompiledContracts

/-!
Test vectors for `Ethereum.SHA256.hash` and the SHA-256 precompile. The checks run when
this module is built (`lake build Ethereum.SHA256Tests`); the library does not import it.
-/

namespace Ethereum.SHA256Tests

private def h (s : String) : String := toHex (SHA256.hash s.toUTF8)

-- The examples of FIPS 180-2, Appendix B, and the empty message.
#guard h "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard h "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard h "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard h ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopq" ++
    "klmnopqrlmnopqrsmnopqrstnopqrstu") ==
  "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"

-- Messages of 55, 56 and 64 bytes, at the padding boundaries.
#guard h (String.ofList (List.replicate 55 'a')) ==
  "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"
#guard h (String.ofList (List.replicate 56 'a')) ==
  "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"
#guard h (String.ofList (List.replicate 64 'a')) ==
  "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"

-- The precompile charges 60 + 12 per word.
private def env (d : ByteArray) : ExecutionEnv := { (default : ExecutionEnv) with calldata := d }

#guard toHex (Ξ_SHA256 default ⟨1000⟩ default (env "abc".toUTF8)).2.2.2 ==
  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard (Ξ_SHA256 default ⟨1000⟩ default (env "abc".toUTF8)).2.1 == ⟨1000 - 72⟩

-- The kernel evaluates the hash.
example : (SHA256.hash "abc".toUTF8).data.toList.take 4 = [0xba, 0x78, 0x16, 0xbf] := by
  decide +kernel

end Ethereum.SHA256Tests
