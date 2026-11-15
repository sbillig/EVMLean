import Ethereum

/-!
Test vectors for the Merkle Patricia trie roots (`Ethereum.trieRoot`, EthLib's `Trie.root` with
Keccak-256), through the functions that compute the storage, state, transaction, receipt and
withdrawal roots.

- `ethereum/tests` `TrieTests` (`trietest`, `trieanyorder`, their secure-trie versions and
  `hex_encoded_securetrie_test`): the keys and values left after each test's insertions and
  deletions, and its root.
- Generated inputs (a fixed splitmix64 stream), with the roots that EVMLean's former Python
  implementation (`Ethereum/EllipticCurvesPy/trie_root.py`) computed for them. That
  implementation failed on a trie in which one key is a proper prefix of another (a
  `NameError` at the branch value); for those inputs the roots are from the same Python with
  that error fixed, and `TrieTests` covers the case independently. No root of Ethereum's has
  such keys: the state and storage keys are 32-byte hashes, and no RLP encoding of an index is a
  prefix of another's.

The checks run when this module is built (`lake build Ethereum.TrieRootTests`); the library does
not import it.
-/

namespace Ethereum.TrieRootTests

/-- splitmix64. -/
abbrev G := StateM UInt64

def next : G UInt64 := modifyGet fun (s : UInt64) =>
  let s := s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), s)

def below (n : Nat) : G Nat := do return (← next).toNat % n

def bytes (n : Nat) : G ByteArray := do
  let mut out := ByteArray.empty
  for _ in [0:n] do out := out.push (← next).toUInt8
  return out

/-- Bytes from a small alphabet, so that keys share prefixes. -/
def sharingBytes (n : Nat) : G ByteArray := do
  let alphabet : Array UInt8 := #[0x00, 0x01, 0x10, 0x11, 0xff]
  let mut out := ByteArray.empty
  for _ in [0:n] do out := out.push alphabet[← below alphabet.size]!
  return out

def word (bits : Nat) : G UInt256 := do
  let mut n := 0
  for _ in [0:4] do n := n * 2 ^ 64 + (← next).toNat
  return .ofNat (n % 2 ^ bits)

/-- `n` distinct keys from a small alphabet with `1 ≤ len ≤ maxLen` bytes, and values of
`1 ≤ len ≤ maxVal` bytes. -/
def rawPairs (n maxLen maxVal : Nat) : G (Array (ByteArray × ByteArray)) := do
  let mut out : Array (ByteArray × ByteArray) := #[]
  let mut tries := 0
  while out.size < n && tries < 100 * n do
    tries := tries + 1
    let k ← sharingBytes (1 + (← below maxLen))
    if out.any (·.1.data == k.data) then continue
    out := out.push (k, ← bytes (1 + (← below maxVal)))
  return out

/-- A storage map of `n` slots: sequential or random keys, nonzero values of at most `bits`
bits. -/
def storage (n : Nat) (sequential : Bool) (bits : Nat) : G Storage := do
  let mut s : Storage := ∅
  for i in [0:n] do
    let k ← if sequential then pure (UInt256.ofNat i) else word 256
    let v ← word bits
    s := s.insert k (if v == .ofNat 0 then .ofNat 1 else v)
  return s

/-- `n` accounts, each with up to `maxSlots` storage slots and up to 99 bytes of code. -/
def accounts (n maxSlots : Nat) : G PersistentAccountMap := do
  let mut m : PersistentAccountMap := ∅
  for _ in [0:n] do
    let a : AccountAddress := Fin.ofNat _ (← word 160).toNat
    let slots ← below (maxSlots + 1)
    let st ← storage slots false (if (← below 2) = 0 then 64 else 256)
    let code ← bytes (← below 100)
    m := m.insert a ⟨← word 64, ← word 128, st, code⟩
  return m

/-- `n` values of `1 ≤ len ≤ maxVal` bytes for an index-keyed trie. -/
def items (n maxVal : Nat) : G (Array ByteArray) := do
  let mut out := #[]
  for _ in [0:n] do out := out.push (← bytes (1 + (← below maxVal)))
  return out

def run {α} (seed : UInt64) (g : G α) : α := (g.run seed).1

def h (s : String) : ByteArray := (ByteArray.ofBlob s).toOption.getD .empty

def hex (r : Option ByteArray) : String := r.elim "none" toHex

def b (l : List Nat) : ByteArray := ⟨l.toArray.map (·.toUInt8)⟩

/-! ## `ethereum/tests` `TrieTests` -/

/-- Each test: its file and name, whether the trie is secure (keys hashed), the keys and values
left after its insertions and deletions, and its root. -/
def trieTests : List (String × Bool × Array (ByteArray × ByteArray) × String) :=
[
  ("trietest/emptyValues", false, #[(h "646f", h "76657262"), (h "686f727365", h "7374616c6c696f6e"), (h "646f6765", h "636f696e"), (h "646f67", h "7075707079")], "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"),
  ("trietest/branchingTests", false, #[], "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"),
  ("trietest/jeff", false, #[(h "0000000000000000000000000000000000000000000000000000000000000045", h "22b224a1420a802ab51d326e29fa98e34c4f24ea"), (h "0000000000000000000000000000000000000000000000000000000000000046", h "67706c2076330000000000000000000000000000000000000000000000000000"), (h "000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6", h "6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000"), (h "0000000000000000000000007ef9e639e2733cb34e4dfc576d4b23f72db776b2", h "4655474156000000000000000000000000000000000000000000000000000000"), (h "000000000000000000000000ec4f34c97e43fbb2816cfd95e388353c7181dab1", h "4e616d6552656700000000000000000000000000000000000000000000000000"), (h "4655474156000000000000000000000000000000000000000000000000000000", h "7ef9e639e2733cb34e4dfc576d4b23f72db776b2"), (h "4e616d6552656700000000000000000000000000000000000000000000000000", h "ec4f34c97e43fbb2816cfd95e388353c7181dab1"), (h "6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000", h "697c7b8c961b56f675d570498424ac8de1a918f6")], "9f6221ebb8efe7cff60a716ecb886e67dd042014be444669f0159d8e68b42100"),
  ("trietest/insert-middle-leaf", false, #[(h "6b6579316161", h "30313233343536373839303132333435363738393031323334353637383930313233343536373839787878"), (h "6b657931", h "30313233343536373839303132333435363738393031323334353637383930313233343536373839566572795f4c6f6e67"), (h "6b6579326262", h "6176616c33"), (h "6b657932", h "73686f7274"), (h "6b6579336363", h "6176616c33"), (h "6b657933", h "31323334353637383930313233343536373839303132333435363738393031")], "cb65032e2f76c48b82b5c24b3db8f670ce73982869d38cd39a624f23d62a9e89"),
  ("trietest/branch-value-update", false, #[(h "616263", h "616263"), (h "61626364", h "61626364")], "7a320748f780ad9ad5b0837302075ce0eeba6c26e3d8562c67ccc0f1b273298a"),
  ("trieanyorder/singleItem", false, #[(h "41", h "6161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161")], "d23786fb4a010da3ce639d66d5e904a11dbc02746d1ce25029e53290cabf28ab"),
  ("trieanyorder/dogs", false, #[(h "646f65", h "7265696e64656572"), (h "646f67", h "7075707079"), (h "646f67676c6573776f727468", h "636174")], "8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3"),
  ("trieanyorder/puppy", false, #[(h "646f", h "76657262"), (h "686f727365", h "7374616c6c696f6e"), (h "646f6765", h "636f696e"), (h "646f67", h "7075707079")], "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"),
  ("trieanyorder/foo", false, #[(h "666f6f", h "626172"), (h "666f6f64", h "62617373")], "17beaa1648bafa633cda809c90c04af50fc8aed3cb40d16efbddee6fdf63c4c3"),
  ("trieanyorder/smallValues", false, #[(h "6265", h "65"), (h "646f67", h "7075707079"), (h "626564", h "64")], "3f67c7a47520f79faa29255d2d3c084a7a6df0453116ed7232ff10277a8be68b"),
  ("trieanyorder/testy", false, #[(h "74657374", h "74657374"), (h "7465", h "7465737479")], "8452568af70d8d140f58d941338542f645fcca50094b20f3c3d8c3df49337928"),
  ("trieanyorder/hex", false, #[(h "0045", h "0123456789"), (h "4500", h "9876543210")], "285505fcabe84badc8aa310e2aae17eddc7d120aabec8a476902c8184b3a3503"),
  ("trietest_secureTrie/emptyValues", true, #[(h "646f", h "76657262"), (h "686f727365", h "7374616c6c696f6e"), (h "646f6765", h "636f696e"), (h "646f67", h "7075707079")], "29b235a58c3c25ab83010c327d5932bcf05324b7d6b1185e650798034783ca9d"),
  ("trietest_secureTrie/branchingTests", true, #[], "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"),
  ("trietest_secureTrie/jeff", true, #[(h "0000000000000000000000000000000000000000000000000000000000000045", h "22b224a1420a802ab51d326e29fa98e34c4f24ea"), (h "0000000000000000000000000000000000000000000000000000000000000046", h "67706c2076330000000000000000000000000000000000000000000000000000"), (h "000000000000000000000000697c7b8c961b56f675d570498424ac8de1a918f6", h "6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000"), (h "0000000000000000000000007ef9e639e2733cb34e4dfc576d4b23f72db776b2", h "4655474156000000000000000000000000000000000000000000000000000000"), (h "000000000000000000000000ec4f34c97e43fbb2816cfd95e388353c7181dab1", h "4e616d6552656700000000000000000000000000000000000000000000000000"), (h "4655474156000000000000000000000000000000000000000000000000000000", h "7ef9e639e2733cb34e4dfc576d4b23f72db776b2"), (h "4e616d6552656700000000000000000000000000000000000000000000000000", h "ec4f34c97e43fbb2816cfd95e388353c7181dab1"), (h "6f6f6f6820736f2067726561742c207265616c6c6c793f000000000000000000", h "697c7b8c961b56f675d570498424ac8de1a918f6")], "72adb52e9d9428f808e3e8045be18d3baa77881d0cfab89a17a2bcbacee2f320"),
  ("trieanyorder_secureTrie/singleItem", true, #[(h "41", h "6161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161616161")], "e9e2935138352776cad724d31c9fa5266a5c593bb97726dd2a908fe6d53284df"),
  ("trieanyorder_secureTrie/dogs", true, #[(h "646f65", h "7265696e64656572"), (h "646f67", h "7075707079"), (h "646f67676c6573776f727468", h "636174")], "d4cd937e4a4368d7931a9cf51686b7e10abb3dce38a39000fd7902a092b64585"),
  ("trieanyorder_secureTrie/puppy", true, #[(h "646f", h "76657262"), (h "686f727365", h "7374616c6c696f6e"), (h "646f6765", h "636f696e"), (h "646f67", h "7075707079")], "29b235a58c3c25ab83010c327d5932bcf05324b7d6b1185e650798034783ca9d"),
  ("trieanyorder_secureTrie/foo", true, #[(h "666f6f", h "626172"), (h "666f6f64", h "62617373")], "1385f23a33021025d9e87cca5c66c00de06178807b96a9acc92b7d651ccde842"),
  ("trieanyorder_secureTrie/smallValues", true, #[(h "6265", h "65"), (h "646f67", h "7075707079"), (h "626564", h "64")], "826a4f9f9054a3e980e54b20da992c24fa20467f1ca635115ef4917be66e746f"),
  ("trieanyorder_secureTrie/testy", true, #[(h "74657374", h "74657374"), (h "7465", h "7465737479")], "aea54fb6c80499674248a462864c420c9d9f3b3d38c879c12425bade1ad76552"),
  ("trieanyorder_secureTrie/hex", true, #[(h "0045", h "0123456789"), (h "4500", h "9876543210")], "bc11c02c8ab456db0c4d2728b6a2a6210d06f26a2ace4f7d8bdfc72ddf2630ab"),
  ("hex_encoded_securetrie_test/test1", true, #[(h "a94f5374fce5edbc8e2a8697c15331677e6ebf0b", h "f848018405f446a7a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), (h "095e7baea6a6c7c4c2dfeb977efac326af552d87", h "f8440101a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a004bccc5d94f4d1f99aab44369a910179931772f2a5c001c3229f57831c102769"), (h "d2571607e241ecf590ed94b12d87c94babe36db6", h "f8440180a0ba4b47865c55a341a4a78759bb913cd15c3ee8eaf30a62fa8d1c8863113d84e8a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), (h "62c01474f089b07dae603491675dc5b5748f7049", h "f8448080a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), (h "2adc25665018aa1fe0e6bc666dac8fc2697ff9ba", h "f8478083019a59a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")], "730a444e08ab4b8dee147c9b232fc52d34a223d600031c1e9d25bfc985cbd797"),
  ("hex_encoded_securetrie_test/test2", true, #[(h "a94f5374fce5edbc8e2a8697c15331677e6ebf0b", h "f84c01880de0b6b3a7622746a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), (h "095e7baea6a6c7c4c2dfeb977efac326af552d87", h "f84780830186b7a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0501653f02840675b1aab0328c6634762af5d51764e78f9641cccd9b27b90db4f"), (h "2adc25665018aa1fe0e6bc666dac8fc2697ff9ba", h "f8468082521aa056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")], "a7c787bf470808896308c215e22c7a580a0087bb6db6e8695fb4759537283a83"),
  ("hex_encoded_securetrie_test/test3", true, #[(h "a94f5374fce5edbc8e2a8697c15331677e6ebf0b", h "f84c01880de0b6b3a7614bc3a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), (h "095e7baea6a6c7c4c2dfeb977efac326af552d87", h "f84880840132b3a0a065fee2fffd7a68488cf7ef79f35f7979133172ac5727b5e0cf322953d13de492a06e5d8fec8b6b9bf41c3fb9b61696d5c87b66f6daa98d5f02ba9361b0c6916467"), (h "0000000000000000000000000000000000000001", h "f8448080a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"), (h "2adc25665018aa1fe0e6bc666dac8fc2697ff9ba", h "f8478083012d9da056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a0c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")], "40b37be88a49e2c08b8d33fcb03a0676ffd0481df54dfebd3512b8ec54f40cad")]

#guard trieTests.all fun (_, secured, kvs, root) =>
  hex (trieRoot (if secured then kvs.map fun (k, v) => (KEC k, v) else kvs)) == root
#guard trieTests.length == 25

/-! ## Generated inputs, with the roots of the former Python implementation -/

-- raw empty
#guard hex (trieRoot #[]) == "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

-- raw empty key
#guard hex (trieRoot #[(b [], b [7])]) == "d366bb1134536da82319aac6561e9b71a25dcb888c3959591876b1dfa9c644a9"

-- raw one 1-byte value
#guard hex (trieRoot #[(b [1], b [2])]) == "40d0cb72098892560f0a6e349bdc55b80501978f965f1994d057086850adabb7"

-- raw one 31-byte value
#guard hex (trieRoot #[(b [1, 2], run 1 (bytes 31))]) == "aed8bce347b764e70158f7166360d896cf788fa1a3783e200ced38f50e977d32"

-- raw one 32-byte value
#guard hex (trieRoot #[(run 2 (bytes 32), run 3 (bytes 32))]) == "fb99e308c1966681027f2921b64f8c6883a2627c0af7e3d749d1e9794b657067"

-- raw one 100-byte value
#guard hex (trieRoot #[(b [0xab], run 4 (bytes 100))]) == "26ba382abcfc882c7a64d3725b70779226de55b5f6b074722eb58fef5b50a36d"

-- raw prefix chain  -- the Python with its NameError fixed
#guard hex (trieRoot #[(b [], b [1]), (b [1], b [2]), (b [1, 2], b [3]),
    (b [1, 2, 3], b [4]), (b [1, 2, 3, 4], run 5 (bytes 40))]) == "4bc42e5fb331a7a3bfc64bb1e7f1a34d04f0fe0e1b90489a9e108f20d6b681d6"

-- raw last nibble
#guard hex (trieRoot ((List.range 16).toArray.map fun i => (b [0xab, 0xcd, i], b [i + 1]))) == "e21a690fba1b6e8bc5a35810e6628a833ced4c9548aed425ff69a1b8a0abc580"

-- raw last nibble long values
#guard hex (trieRoot ((List.range 16).toArray.map fun i =>
    (b [0xab, 0xcd, i], run (i.toUInt64 + 10) (bytes 33)))) == "8ac4ed77b47d9c0245efb76287d4dcf114549a0d0f61c9b169945f804088d5d8"

-- raw do dog doge horse  -- the Python with its NameError fixed
#guard hex (trieRoot #[("do".toUTF8, "verb".toUTF8), ("dog".toUTF8, "puppy".toUTF8),
    ("doge".toUTF8, "coin".toUTF8), ("horse".toUTF8, "stallion".toUTF8)]) == "5991bb8c6514148a29db676a14ac506cd2cd5775ace63c30a4fe457715e9ac84"

-- raw random 2
#guard hex (trieRoot (run 102 (rawPairs 2 6 80))) == "b58056337786891e704572adb32770ef0633a79ce91aef7c1880c80dc0ff4508"

-- raw random 3
#guard hex (trieRoot (run 103 (rawPairs 3 6 80))) == "5ec03a267a6c0dd5e68015532d42aaa609de52a47f69ff2b1d1b4c8fc1e18265"

-- raw random 5
#guard hex (trieRoot (run 105 (rawPairs 5 6 80))) == "9a7c23e8025283d693382a889a7d53d7c11eb6675f5eb5774eef7cfe9c75a066"

-- raw random 16  -- the Python with its NameError fixed
#guard hex (trieRoot (run 116 (rawPairs 16 6 80))) == "eaca0939fe7026952d0401a9e5c8600d35cc0e41854adc588db2e4d1a05410d6"

-- raw random 17  -- the Python with its NameError fixed
#guard hex (trieRoot (run 117 (rawPairs 17 6 80))) == "ab6f2c583acb9c05a63e47f1782b3e041043cdee12c7cfecb55d60220874be7e"

-- raw random 64  -- the Python with its NameError fixed
#guard hex (trieRoot (run 164 (rawPairs 64 6 80))) == "54a695d3cbaad64c8961147a1430a63b7ee934769313b1060ffdbd019ef09fad"

-- raw random 256  -- the Python with its NameError fixed
#guard hex (trieRoot (run 356 (rawPairs 256 6 80))) == "4662012237b6b4e6fc021fb6e3e3d8fb2309f7932c26f10d0a1f35d7df134d06"

-- raw random 300  -- the Python with its NameError fixed
#guard hex (trieRoot (run 400 (rawPairs 300 6 80))) == "0c661f770a26f881293c659ca7a388a088929b374eff85c3c814a94e5dc06e57"

-- storage 0 sequential 8
#guard hex (computeTrieRoot (run 208 (storage 0 true 8))) == "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

-- storage 1 sequential 8
#guard hex (computeTrieRoot (run 209 (storage 1 true 8))) == "04276512d4dd54231fe4f4207cad7fb1c21fa6b251a12a5e3dc70e2734222336"

-- storage 1 random 256
#guard hex (computeTrieRoot (run 457 (storage 1 false 256))) == "a328ea028c45acff42e4b65032f088c02c20436ccaef399491bc85a5d03cb9b8"

-- storage 2 random 8
#guard hex (computeTrieRoot (run 210 (storage 2 false 8))) == "aab329262969f926fea3a41ff0e2c1cb3ebb569d86548645c063591fa679a36a"

-- storage 3 sequential 256
#guard hex (computeTrieRoot (run 459 (storage 3 true 256))) == "6319ebe88c48233df92865dbe518ff3e9a84bc6173c7eef00fdc9dae43043b78"

-- storage 10 sequential 64
#guard hex (computeTrieRoot (run 274 (storage 10 true 64))) == "a748ccecd32f31916c97073eb708ac94f5a22cc49cf62b9fed0eb36614ab5ccc"

-- storage 16 random 256
#guard hex (computeTrieRoot (run 472 (storage 16 false 256))) == "234d0ccfaa427d57dcc33d08796899b6478ba6d34ef08b0448d63e3da1220e67"

-- storage 17 sequential 8
#guard hex (computeTrieRoot (run 225 (storage 17 true 8))) == "855cb57651fff481c8ccc05080d23ba640495b13b1c83d612c7506aea8b90fd2"

-- storage 100 random 256
#guard hex (computeTrieRoot (run 556 (storage 100 false 256))) == "c576c6907a5db43f3d213a8b140901fd725d1aeb4e5c510d0ef777857ef0a5b5"

-- storage 100 sequential 8
#guard hex (computeTrieRoot (run 308 (storage 100 true 8))) == "dbab0e9a27b8d1351c66a7d677497628ccdae5369a79b6b81c96ceadc0deac68"

-- storage 300 random 64
#guard hex (computeTrieRoot (run 564 (storage 300 false 64))) == "81c1014039108cbdb2eef827688d1c30d5707159f8b09b4a44ed1014abc7bd6d"

-- state 0 accounts, up to 0 slots
#guard hex (stateTrieRoot (run 300 (accounts 0 0))) == "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

-- state 1 accounts, up to 0 slots
#guard hex (stateTrieRoot (run 301 (accounts 1 0))) == "75b14063d228eeb0f76afbc80dd547016ceebc336428d7754faf16dee459e290"

-- state 1 accounts, up to 5 slots
#guard hex (stateTrieRoot (run 306 (accounts 1 5))) == "66419fed53ead406b4578574d2831eb215e4a4b8b7fbcb7144ae4b50350b86e8"

-- state 2 accounts, up to 3 slots
#guard hex (stateTrieRoot (run 305 (accounts 2 3))) == "1b08b07c16c46d04fa41594d6ce9043d74ee39aaf59d53eea6440592e768b23f"

-- state 5 accounts, up to 5 slots
#guard hex (stateTrieRoot (run 310 (accounts 5 5))) == "f867703bb4812309675b24783e5a87067044a1d8af90d0aa40cfeb460d244a5f"

-- state 20 accounts, up to 10 slots
#guard hex (stateTrieRoot (run 330 (accounts 20 10))) == "30f9a8ad8106f5aed4065c1fd4f0fcf09f0f8064e62494dd8954db6b09ba9b2a"

-- state 100 accounts, up to 4 slots
#guard hex (stateTrieRoot (run 404 (accounts 100 4))) == "185bd9a9b1b07ab1383f81a45d10791e84e47d6f5a6fcb2d5eb2acce50ed9fcb"

-- index 0 values up to 10 bytes
#guard hex (Transaction.computeTrieRoot (run 410 (items 0 10))) == "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

-- index 1 values up to 10 bytes
#guard hex (TransactionReceipt.computeTrieRoot (run 411 (items 1 10))) == "57d6a5d4cd1fba9d722dd8bb905f726cd9a452881bd22eb57cd543c6da28055f"

-- index 1 values up to 120 bytes
#guard hex (Withdrawal.computeTrieRoot (run 521 (items 1 120))) == "45370778077db69e4592d5d0bf3e6f91af99c94e8cf9b94f823881c13c30a43a"

-- index 2 values up to 20 bytes
#guard hex (Transaction.computeTrieRoot (run 422 (items 2 20))) == "609dca1c455fca7ebeb3708fd106789bdfe2a79677d050f3087968ff9cce925b"

-- index 15 values up to 40 bytes
#guard hex (TransactionReceipt.computeTrieRoot (run 455 (items 15 40))) == "046584cd939f69885c8f1bfd36d5ddac8e85c3abd87a1b1020c133e65ba31f5f"

-- index 16 values up to 40 bytes
#guard hex (Withdrawal.computeTrieRoot (run 456 (items 16 40))) == "df4f47a781739964b1e8b456134e458098a16d16f2a4231558605176327eadab"

-- index 17 values up to 40 bytes
#guard hex (Transaction.computeTrieRoot (run 457 (items 17 40))) == "607ae0eb3758181aba5e6de81a4161b97b0f108c4cfc04c229e46c60e6a8cffb"

-- index 127 values up to 31 bytes
#guard hex (TransactionReceipt.computeTrieRoot (run 558 (items 127 31))) == "ba27918141d1dd3a0428c8149bbe2e79098b465d719626420b19590797b2662f"

-- index 128 values up to 32 bytes
#guard hex (Withdrawal.computeTrieRoot (run 560 (items 128 32))) == "e32bfa06a00da49948fb8a1339b87191c894963c676d982cb30b6ddcd7eec15e"

-- index 129 values up to 120 bytes
#guard hex (Transaction.computeTrieRoot (run 649 (items 129 120))) == "889d66c8e06c21a400f5f6c5e75000fc51cf6f7bfe1193db7d6755c96bdb408e"

-- index 200 values up to 120 bytes
#guard hex (TransactionReceipt.computeTrieRoot (run 720 (items 200 120))) == "0af988f95627155f8a925001baba105f8b58f4e2886cc079be554ed57dc6109e"

-- index 300 values up to 60 bytes
#guard hex (Withdrawal.computeTrieRoot (run 760 (items 300 60))) == "1f77aaa0761b7227c97fefb5b83b12d0472802aba6b51dae536929147bb9e1bf"
-- The differential also compared 300 accounts with up to 2 slots each (root
-- 875541eb7761930e4aed3fca3980f1c641f4e47d649a0536614ede5f3cd71c19); it takes about a minute
-- in the interpreter, so it is left out here.

end Ethereum.TrieRootTests
