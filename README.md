This repository contains a formal model of the EVM in Lean 4.
It is an EVM-focused port of Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) to a newer version of
Lean, with the Yul model removed.
The aim is to simplify proof development over the model.

Everything here is work in progress and is subject to change therefore.

The changes in this repository are intended to ease proof development over the
EVM model, with some tradeoffs against executable performance. They do not
relax the behavioral compatibility target: the model continues to pass the same
pinned Ethereum conformance suite and test driver used by the EVMYulLean
baseline. For a summary of the main differences from Nethermind's
upstream project, see
[nethermind-changes.md](nethermind-changes.md).

# Requirements
Lean (through `elan`) only: no Lean code runs Python or another external process.

# Project structure

## Primops
The `Operation` describing all of the primitive operations:
```
Ethereum/Operations.lean
```

## EVM
The model of the EVM state `EVM.State`:
```
Ethereum/State.lean
```

The semantic function `step`:
```
Ethereum/Semantics.lean
```

## Forks
The model follows Cancun, plus Osaka's `CLZ` (EIP-7939). A block header's
`fork` field (`Ethereum.Fork`, default `Cancun`) says which rules apply: under
`Cancun`, `0x1e` is an invalid instruction; under `Osaka` it is `CLZ`. RLP
encodings do not carry the fork, so decoded blocks are Cancun's, as are the
conformance tests.

## Cryptographic trust boundaries

Ethereum's Keccak-256 is implemented as transparent Lean in
[`Ethereum/SpongeHash/Keccak256.lean`](Ethereum/SpongeHash/Keccak256.lean).
The implementation includes Keccak-f[1600], Ethereum's legacy `0x01` domain
suffix, multi-block absorption, and a proof that every digest contains exactly
32 bytes. It is exposed as `Ethereum.Keccak256.hash`, with `Ethereum.KEC` used
by the executable EVM semantics. Keccak calls reachable from the semantics
therefore do not cross an FFI boundary.

Public-key recovery on secp256k1, `ECDSARECOVER`, is also transparent Lean. It
is used by the ECRECOVER precompile and by the conformance runner to recover
transaction senders. The implementation in
[`Ethereum/Secp256k1/Impl.lean`](Ethereum/Secp256k1/Impl.lean) computes on
natural numbers in Jacobian coordinates. It is proved equal, for all inputs, to
the specification in [`Ethereum/Secp256k1/Spec.lean`](Ethereum/Secp256k1/Spec.lean),
which states recovery over Mathlib's group of points of `y² = x³ + 7` over
`ZMod p`; the proof is in [`Ethereum/Secp256k1/Proofs`](Ethereum/Secp256k1/Proofs).
The primality of `p` and of the group order `n` is checked by the kernel from
Pratt certificates. [`Ethereum/Theory/ECRecover.lean`](Ethereum/Theory/ECRecover.lean)
states the result of the precompile in terms of the specification.

The alt_bn128 addition and scalar multiplication precompiles (ECADD and ECMUL)
are specified in [`Ethereum/BN254/Spec.lean`](Ethereum/BN254/Spec.lean) over
Mathlib's points of `y² = x³ + 3`, with the point decoding of EIP-196, and
implemented and proved in the same way; [`Ethereum/Theory/BN254.lean`](Ethereum/Theory/BN254.lean)
states the precompiles' results. Both curves share the field arithmetic, point
formulas, scalar multiplication and their proofs in
[`Ethereum/Weierstrass`](Ethereum/Weierstrass).

RIPEMD-160 and SHA-256 are transcribed in
[`Ethereum/RIPEMD160.lean`](Ethereum/RIPEMD160.lean) and
[`Ethereum/SHA256.lean`](Ethereum/SHA256.lean); each definition is both the
specification and the implementation. BLAKE2 F is specified in
[`Ethereum/BLAKE2.lean`](Ethereum/BLAKE2.lean) as RFC 7693's compression function
with EIP-152's input format; a faster implementation of its rounds is proved
equal to the specification and runs in compiled code through a `@[csimp]` lemma.

MODEXP is specified in [`Ethereum/Modexp/Spec.lean`](Ethereum/Modexp/Spec.lean): EIP-198's
input format and `base ^ exponent mod modulus` on natural numbers, written to the modulus'
length, with EIP-2565's gas. `Ξ_EXPMOD_eq` ([`Ethereum/Theory/Modexp.lean`](Ethereum/Theory/Modexp.lean))
states the precompile in terms of it; the implementation computes by square-and-multiply.

The pairing check (ECPAIRING, `0x08`) and the point evaluation precompile (`0x0a`) are
EthLib's specifications ([ethereum/EthLib](https://github.com/ethereum/EthLib), pinned in
`lake-manifest.json`): `Ξ_SNARKV` calls its `ecpairing` and `Ξ_PointEval` its
`pointEvaluation`. [`Ethereum/Theory/SNARKV.lean`](Ethereum/Theory/SNARKV.lean) and
[`Ethereum/Theory/PointEval.lean`](Ethereum/Theory/PointEval.lean) state their gas and output
in terms of EthLib's decoders, pairing check and KZG check. EthLib proves properties of those
definitions (its `SOUNDNESS.md`); EVMLean's theorems use only the definitions.

The roots of the Merkle Patricia tries (the state and storage roots, and the transaction,
receipt and withdrawal roots) are EthLib's `Trie.root` with `KEC`, through `Ethereum.trieRoot`
([`Ethereum/Trie.lean`](Ethereum/Trie.lean)). [`Ethereum/TrieRootTests.lean`](Ethereum/TrieRootTests.lean)
checks it on `ethereum/tests`' `TrieTests` and on generated inputs.

## Conformance testing
A git submodule with EVM conformance tests is in:
```
EthereumTests/
```

The test running infrastructure can be found in:
```
Conform/
```

Passing this suite is the baseline behavioral trust check for the executable EVM
model. Any changes are accepted under the constraint that these
conformance tests continue to pass.

To execute conformance tests, make sure the `EthereumTests` directory is the appropriate git submodule and run:
```
lake test -- <NUM_THREADS> 2> out_discard.txt
```
where `<NUM_THREADS>` is the number of threads running conformance tests in parallel. Note that the default is `1`.
We recommend redirecting `stderr` into a file to not pollute the output.

# License

This repository is based on Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean), which is licensed under the Apache License, Version 2.0. This modified copy is distributed under the Apache License, Version 2.0; see [LICENSE](LICENSE).

Notable modifications include porting the project to a newer Lean version, stripping the Yul portions, and adapting the remaining EVM model and project structure for proof development. See [NOTICE](NOTICE) for attribution and modification notes.

Some included third-party components carry their own licenses, including `EthereumTests/LICENSE` and `keccak256/LICENSE`.
