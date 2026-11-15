# EVM Proof Development

This directory contains proofs about the EVM model defined under `Ethereum`.
The files are organized by the property being established rather than by EVM
component.

## Files

- [`OpcodeLemmas.lean`](OpcodeLemmas.lean) gives explicit characterizations of
  `step` for individual opcodes. These results provide a convenient starting
  point for proofs about concrete instructions.

- [`GasLemmas.lean`](GasLemmas.lean) establishes positivity, monotonicity, and
  decrease properties for gas costs and carries them through `Z`, `step`,
  `Xstep`, `X`, calls, and precompiled contracts.

- [`NoOutOfFuel.lean`](NoOutOfFuel.lean) separates the model's recursion fuel
  from EVM gas. In particular, it shows that execution with fuel derived from
  the available gas cannot fail with the artificial `OutOfFuel` exception.

- [`ProgressLemmas.lean`](ProgressLemmas.lean) relates `Xstep` to the recursive
  opcode loop `X`. It also defines `XstepN`, a relation describing finite
  sequences of steps.

- [`ReturnDataBound.lean`](ReturnDataBound.lean) derives bounds on return-data
  size from the available gas and propagates them through calls, contract
  creation, and precompiled contracts. Transparent Lean wrappers reject
  externally computed precompile results of an unexpected size, so these
  proofs require no custom axioms about the output lengths of the external
  implementations.

- [`ECRecover.lean`](ECRecover.lean) states `ECDSARECOVER` and the ECRECOVER
  precompile `Ξ_ECREC` in terms of the specification of secp256k1 public-key
  recovery in `Ethereum/Secp256k1/Spec.lean`.

- [`RIP160.lean`](RIP160.lean), [`SHA256.lean`](SHA256.lean),
  [`BLAKE2.lean`](BLAKE2.lean) and [`BN254.lean`](BN254.lean) state the RIPEMD-160,
  SHA-256, BLAKE2 F, ECADD and ECMUL precompiles in terms of their Lean
  definitions and the specifications in `Ethereum/BN254/Spec.lean`.

- [`Modexp.lean`](Modexp.lean) states the MODEXP precompile `Ξ_EXPMOD` in terms of the
  specification in `Ethereum/Modexp/Spec.lean`: EIP-198 and EIP-2565 under `Cancun`
  (`Ξ_EXPMOD_eq`), with EIP-7823's bound and EIP-7883's price under `Osaka`
  (`Ξ_EXPMOD_eq_osaka`).

- [`P256Verify.lean`](P256Verify.lean) states the P256VERIFY precompile `Ξ_P256VERIFY`
  (EIP-7951) in terms of EthLib's input checks and secp256r1 ECDSA verification.

- [`Forks.lean`](Forks.lean) states that under `Cancun` the precompile addresses, the
  initial accessed accounts and `Θ`'s dispatch are Cancun's.

- [`AccountLocality.lean`](AccountLocality.lean) develops relations describing
  which changes to an account are consistent with EVM execution and carries
  them through steps, calls, and contract creation. **The intended locality
  property for effects after calls is work in progress, including its formal
  statement. The current relations and theorems should not yet be treated as a
  definitive formulation of that property.**

- [`StaticStorage.lean`](StaticStorage.lean) proves preservation results for
  static execution, including that static calls preserve persistent storage,
  transient storage, and account code.

All modules are imported by `Ethereum.lean`. The directory is active proof
development, so theorem interfaces and file boundaries may still change.
