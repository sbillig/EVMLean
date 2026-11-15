import Ethereum.Semantics
import Ethereum.Theory.Modexp

/-!
What the block header's `fork` changes outside `step`, and that under `Cancun` each changed
definition is the Cancun one: the precompile addresses `π` and with them the initial accessed
accounts `A0` and `toExecute`, which reads `π fork`, `Θ`'s dispatch (P256VERIFY at `0x100`, EIP-7951), and MODEXP
(EIP-7823, EIP-7883; `Ξ_EXPMOD_eq` and `Ξ_EXPMOD_eq_osaka` in `Ethereum/Theory/Modexp.lean`).
`CLZ` is in `step` (`step_clz`, `step_clz_cancun`).
-/

namespace Ethereum

open EVM

/-- Cancun's precompile addresses, `1` to `10`. -/
theorem π_Cancun :
    π .Cancun = RBTree.RBSet.ofList ((List.range 11).tail.map (Fin.ofNat _)) compare := rfl

/-- Osaka adds P256VERIFY at `0x100`. -/
theorem π_Osaka :
    π .Osaka =
      RBTree.RBSet.ofList ((List.range 11).tail.map (Fin.ofNat _) ++ [Fin.ofNat _ 0x100])
        compare := rfl

theorem A0_Cancun :
    A0 .Cancun = { (default : Substate) with
      accessedAccounts := RBTree.RBSet.ofList ((List.range 11).tail.map (Fin.ofNat _)) compare } :=
  rfl

/-- Before Osaka, `Θ` does not run P256VERIFY: at `0x100` it gives what it gives at any other
address without a precompile, here `0`. -/
theorem Θ_P256VERIFY_cancun (σ σ₀ : AccountMap) (A : Substate) (s o r : AccountAddress)
    (g p v v' : UInt256) (d : ByteArray) (e : Fin 1025) (H : BlockHeader)
    (blobVersionedHashes : List ByteArray) (blocks : ProcessedBlocks) (w : Bool)
    (hfork : H.fork = .Cancun) :
    Θ σ σ₀ A s o r (.Precompiled (Fin.ofNat _ 0x100)) g p v v' d e H blobVersionedHashes blocks w =
      Θ σ σ₀ A s o r (.Precompiled 0) g p v v' d e H blobVersionedHashes blocks w := by
  have h : ¬ (H.fork = Fork.Osaka) := by rw [hfork]; decide
  unfold Θ
  simp only [h, ↓reduceIte]
  rfl

end Ethereum
