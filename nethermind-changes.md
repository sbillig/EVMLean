# Main Changes from Nethermind's EVMYulLean

This repository is derived from Nethermind's
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean), but has a narrower
focus: supporting proof development over the EVM semantics.

The changes favor definitions that are easier to inspect and reason about in
Lean. Some of them trade executable performance for simpler proof obligations
or a smaller trusted surface. They do not relax the behavioral compatibility
target: the EVM model continues to pass the Ethereum conformance tests used by
the original project.

This document summarizes the main conceptual differences. It is not intended to
be an exhaustive file-by-file changelog.

## Updated Lean Version

The project was ported to a newer version of Lean. The resulting compatibility
changes are not intended to alter the modeled EVM behavior.

## EVM-Only Model

The Yul model and its tests were removed. The generic layer that distinguished
EVM operations and state from their Yul counterparts was also specialized to
the EVM.

As part of this change, the previous split between generic state, shared machine
state, and EVM state was simplified into the EVM-specific structures in
`Ethereum/State.lean` and `Ethereum/MachineState.lean`. This removes Yul-related
parameters and projections from EVM proofs, at the cost of no longer providing
Yul semantics.

## Reduced Use of Fuel

The original model threaded an explicit fuel argument through most of the
execution semantics. Reaching zero fuel produced an `OutOfFuel` exception,
independently of the EVM's own gas and call-depth limits.

In this repository, recursive message calls and contract creation instead use
the EVM call-depth bound to justify termination. The outer opcode loop `X`
retains fuel, but its caller derives that fuel from the available gas rather
than exposing an independent execution parameter.

This makes the high-level semantics less dependent on an artificial termination
mechanism while preserving a structurally recursive opcode loop. The associated
proof in `Ethereum/Theory/NoOutOfFuel.lean` connects fuel exhaustion to gas
consumption.

## Zero-Saturating Gas

Available gas was changed from `UInt256`, whose subtraction wraps modulo
`2^256`, to the zero-saturating `Sat256` type in `Ethereum/Sat256.lean`.
Out-of-gas checks still occur before gas is charged.

The new representation prevents modular underflow from appearing in
intermediate definitions and provides simpler monotonicity and subtraction
lemmas for proofs.

## Transparent `ByteArray.zeroes`

The original `ByteArray.zeroes` was an opaque Lean function implemented through
the C FFI. It is now defined transparently in Lean using `Array.replicate`.

This is slower during execution, but it lets proofs inspect the definition
directly and removes one foreign primitive from the trusted surface. The change
is contained primarily in `Ethereum/Wheels.lean` and `Ethereum/FFI/ffi.lean`.

## Pure Lean Ethereum Keccak-256

The Keccak-256 operation used throughout the EVM semantics was moved from an
opaque C FFI declaration to the transparent implementation in
`Ethereum/SpongeHash/Keccak256.lean`. It implements the 24 rounds of
Keccak-f[1600] over a 25-lane `UInt64` state, the 1088-bit sponge rate,
little-endian lane encoding, and Ethereum's legacy `0x01` padding suffix. Both
single- and multi-block inputs are handled, including the final-rate-byte
`0x81` padding case.

The implementation exposes `Ethereum.Keccak256.round`,
`Ethereum.Keccak256.permute`, and `Ethereum.Keccak256.hash`; `Ethereum.KEC` is
the name used by the executable semantics and replaces the former `ffi.KEC`
name. The state and rate-block dimensions are represented by fixed-size
vectors, and `hash_size_eq_32` proves the output size. This reduces the trusted
surface and makes concrete Keccak computations available to kernel reduction,
at a significant executable-performance cost relative to the C implementation.
It is not yet a mathematical proof that the implementation refines an
independent Keccak specification. We trust that the implementation is valid
by conformance to the EEST.

The third-party C Keccak source remains in the build configuration for now,
but no Keccak call reachable from the production EVM semantics uses it.

## Pure Lean secp256k1 Public-Key Recovery

`ECDSARECOVER` previously ran `Ethereum/EllipticCurvesPy/recover.py` through
`totallySafePerformIO`. Compiled code depended on Python and `coincurve`, and in
the logic the function returned `Inhabited.default`, so theorems about the
ECRECOVER precompile were about a precompile that recovers no key.

It is now computed by `Ethereum.Secp256k1.recover` in
`Ethereum/Secp256k1/Impl.lean`: arithmetic on natural numbers modulo `p`,
Jacobian coordinates, and one chain of doublings for `u₂ R - u₁ G`. The
specification in `Ethereum/Secp256k1/Spec.lean` states recovery as
`r⁻¹ (s R - e G)` over Mathlib's `WeierstrassCurve` points of `y² = x³ + 7` over
`ZMod p`, and the precompile's output as the Keccak-256 address of that key.
`Ethereum.Secp256k1.recover_eq` proves that the implementation computes the
specification for all inputs, in layers: field operations against `ZMod p`,
point doubling and addition against Mathlib's Jacobian formulas, scalar
multiplication against `•`, and the square root and parity choice. Mathlib's
group law needs `ZMod p` to be a field; `p_prime` and `n_prime` are Pratt
certificates whose modular powers the kernel evaluates. `Ethereum.ECDSARECOVER_eq`
and `Ethereum.Ξ_ECREC_eq` (`Ethereum/Theory/ECRecover.lean`) restate
`ECDSARECOVER` and `Ξ_ECREC` in terms of the specification. Recovery takes a few
milliseconds compiled and about a quarter of a second in the kernel.

`ECDSARECOVER` accepts the recovery identifiers 0 and 1 only. `recover.py`
passed 2 and 3 on to libsecp256k1, which then tries the abscissa `r + n`; no
caller passes them. `ECDSASIGN`, which ran `sign.py` and which nothing called,
was removed with `recover.py`, so the Python package `coincurve` is no longer
needed.

## Pure Lean RIPEMD-160, ECADD and ECMUL

`RIP160`, `BN_ADD` and `BN_MUL` previously ran `rip160.py`, `bn_add.py` and
`bn_mul.py` through `totallySafePerformIO`, and in the logic returned
`Inhabited.default`. RIPEMD-160 is now transcribed over 32-bit words in
`Ethereum/RIPEMD160.lean`. ECADD and ECMUL are specified over Mathlib's points of
alt_bn128, `y² = x³ + 3` over `ZMod p`, with EIP-196's decoding (coordinates below
`p`, `(0, 0)` for the point at infinity, the curve equation), in
`Ethereum/BN254/Spec.lean`, and `Ethereum/BN254/Proofs.lean` proves the
implementation equal to the specification. The field arithmetic, Jacobian point
formulas, scalar multiplication and their proofs are shared with secp256k1 in
`Ethereum/Weierstrass`, with the prime and the curve constant as parameters.
`Ξ_RIP160_eq`, `Ξ_BN_ADD_eq` and `Ξ_BN_MUL_eq` (`Ethereum/Theory`) state the
precompiles' results.

Five unused constants in `PrecompiledContracts.lean` (`expmodOutput`,
`bn_addOutput₀`, `bn_addOutput₁`, `bn_mulOutput`, `snarkvOutput`) were removed.
As closed terms they were evaluated when the module was initialised, so every
program linking EVMLean ran `bn_add.py` twice, `bn_mul.py` and `snarkv.py`
before `main`.

## SHA-256 and BLAKE2 F

`ffi.SHA256` and `ffi.BLAKE2` called C functions through `@[extern]` on `opaque`
constants, so in the logic their results were unspecified. SHA-256 is now a
transcription of FIPS 180-4 in `Ethereum/SHA256.lean`, which runs about as fast
as the C library it replaces; the `sha-2` library is no longer built. BLAKE2 F is
specified in `Ethereum/BLAKE2.lean` (RFC 7693's `F` with a rounds parameter, and
EIP-152's input format). The precompile's maximum-rounds test runs `2³² - 1`
rounds, which the specification, on arrays of boxed words, computes about three
times slower than the C function that ran it before. `roundsFast` keeps the sixteen
words of the working vector as the scalar fields of one structure, updated in
place, with each round's permutation written out; `round_eq`, `rounds_eq` and
`F_eq_Ffast` prove it equal to the specification, and the `@[csimp]` lemma
`compressInput_eq_fast` makes compiled code run it. It is faster than the C
function was, so `blake2compressb64` was removed from `Ethereum/FFI/ffi.c`, and
no C code is trusted for BLAKE2 F. `Ξ_SHA256_eq` and `Ξ_BLAKE2_F_eq`
(`Ethereum/Theory`) state the precompiles' results. The unused Python wrappers
`Ethereum/SHA256.lean` (replaced) and `Ethereum/BLAKE2_F.lean` were removed.

## Checked External Precompile Outputs

The other externally implemented cryptographic precompiles remain opaque. A
transparent Lean boundary in `Ethereum/PrecompileOutput.lean` now accepts a
successful external result only when it has the prescribed size. The checks
cover the SNARKV output at 32 bytes and the point evaluation output at 64 bytes. An external implementation that returns a malformed length is treated
as an error rather than allowing that value into the EVM semantics.

These checks let `Ethereum/Theory/ReturnDataBound.lean` prove its precompile
return-size bounds without custom axioms about the outputs of C or
process-backed implementations. The checks constrain output shape only; the
cryptographic correctness of those external implementations remains outside
the Lean proof.

## Added `Xstep`

The body of the opcode loop was factored into `Xstep`, representing one opcode
in the current call frame. The recursive loop `X` is then expressed by repeated
applications of this step.

An `Xstep` can still execute a nested message call or contract creation when the
current opcode requires it. The boundary is nevertheless useful for stating
per-opcode properties and reasoning about finite execution sequences.

The definitions are in `Ethereum/Semantics.lean`, with supporting results in
`Ethereum/Theory/ProgressLemmas.lean` and
`Ethereum/Theory/GasLemmas.lean`.

## Simplified Exception Paths

After recursive calls were moved away from explicit fuel, `Lambda` and `Theta`
no longer needed to return exceptions solely to carry fuel exhaustion. They now
return their semantic results directly, while exceptional execution of nested
EVM code is still represented as a failed call or contract creation.

This also follows the presentation in the
[Yellow Paper](https://ethereum.github.io/yellowpaper/paper.pdf), where
`Lambda` and `Theta` return semantic result tuples rather than propagating a
separate exception result.

This does not remove EVM exceptions generally. Opcode-level exceptional halts
and the exception result of the opcode loop remain part of the model.

## Osaka's `CLZ`

`CLZ` (EIP-7939, opcode `0x1e`) is decoded, priced (`Glow`) and stepped like the
other bitwise operations, but `step` executes it only when the block header's
new `fork` field is `Osaka`; under the default `Cancun` it fails with an invalid
instruction, so Cancun's behavior is unchanged. The fork rides on the header
because `Θ`, `Lambda` and `Υ` already pass the header to every nested frame.

## Added EVM Proof Library

The [`Ethereum/Theory`](Ethereum/Theory/README.md) directory contains the proof
development built over the EVM model. It includes results about opcode behavior,
gas consumption, execution progress, account locality, storage preservation and
extensionality, and return-data bounds.
