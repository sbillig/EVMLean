import Ethereum.BN254.Spec
import Ethereum.Weierstrass.Proofs.MulAdd

/-!
`Ethereum.BN254.add` and `Ethereum.BN254.mul` compute `Spec.add` and `Spec.mul`, for
all inputs. The proof uses the curve-generic layers of `Ethereum/Weierstrass/Proofs`.
-/

namespace Ethereum.BN254

open Spec Weierstrass

private theorem three_lt_p : 3 < p := by decide

private theorem p_pos : 0 < p := by decide

private theorem three_ne_zero : (3 : ZMod p) ≠ 0 :=
  mod_cast natCast_ne_zero (k := 3) (by norm_num) three_lt_p

/-- `decode` returns a valid point, standing for the point `Spec.decode` specifies. -/
theorem decode_spec (x y : ℕ) :
    (∀ P ∈ decode x y, P.Valid (3 : ZMod p)) ∧
      (decode x y).map (Point.toSpec (3 : ZMod p)) = Spec.decode x y := by
  unfold decode Spec.decode
  split_ifs with hr h0 hc hc' hc'
  · refine ⟨fun P hP => ?_, ?_⟩
    · obtain rfl := Option.some.inj hP
      exact infinity_valid
    · rw [Option.map_some, infinity_toSpec]
  · -- `(x, y)` satisfies the equation.
    have he : (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + 3 := by
      have := congrArg (fun a : ℕ => (a : ZMod p)) hc
      simp only [natCast_fmul, natCast_fadd, Nat.cast_ofNat] at this
      linear_combination this
    refine ⟨fun P hP => ?_, ?_⟩
    · obtain rfl := Option.some.inj hP
      exact affine_valid three_lt_p three_ne_zero he
    · rw [Option.map_some, affine_toSpec three_lt_p three_ne_zero he]
  · exfalso
    refine hc' ((nonsingular_iff three_lt_p three_ne_zero _ _).mpr ?_)
    have := congrArg (fun a : ℕ => (a : ZMod p)) hc
    simp only [natCast_fmul, natCast_fadd, Nat.cast_ofNat] at this
    linear_combination this
  · exfalso
    refine hc ((natCast_inj (fmul_lt p_pos _ _) (fadd_lt p_pos _ _)).mp ?_)
    have := (nonsingular_iff three_lt_p three_ne_zero _ _).mp hc'
    simp only [natCast_fmul, natCast_fadd, Nat.cast_ofNat]
    linear_combination this
  · exact ⟨fun _ h => (nomatch h), rfl⟩
  · exact ⟨fun _ h => (nomatch h), rfl⟩

/-- `encode` encodes the point that a valid `P` stands for. -/
theorem encode_spec {P : Weierstrass.Point} (hP : P.Valid (3 : ZMod p)) :
    encode P = Spec.encode (P.toSpec (3 : ZMod p)) := by
  unfold encode
  rw [toAffine_spec (by decide) hP]
  rcases P.toSpec (3 : ZMod p) with _ | ⟨x, y, _⟩ <;> rfl

/-- The implementation of ECADD computes its specification. -/
theorem add_eq (x₀ y₀ x₁ y₁ : ℕ) : add x₀ y₀ x₁ y₁ = Spec.add x₀ y₀ x₁ y₁ := by
  obtain ⟨hv₀, hs₀⟩ := decode_spec x₀ y₀
  obtain ⟨hv₁, hs₁⟩ := decode_spec x₁ y₁
  unfold add Spec.add
  rw [← hs₀, ← hs₁]
  rcases h₀ : decode x₀ y₀ with _ | P
  · rfl
  rcases h₁ : decode x₁ y₁ with _ | Q
  · rfl
  have hP := hv₀ P (by rw [h₀]; rfl)
  have hQ := hv₁ Q (by rw [h₁]; rfl)
  change some (encode (P.add p Q)) =
    some (Spec.encode (P.toSpec (3 : ZMod p) + Q.toSpec (3 : ZMod p)))
  rw [encode_spec (hP.add hQ), toSpec_add hP hQ]

/-- The implementation of ECMUL computes its specification. -/
theorem mul_eq (x y k : ℕ) : mul x y k = Spec.mul x y k := by
  obtain ⟨hv, hs⟩ := decode_spec x y
  unfold mul Spec.mul
  rw [← hs]
  rcases h : decode x y with _ | P
  · rfl
  have hP := hv P (by rw [h]; rfl)
  obtain ⟨hQv, hQ⟩ := mulAdd_spec hP infinity_valid hP
    (by rw [infinity_toSpec, add_zero]) (k.log2 + 1) k 0 Nat.lt_log2_self (Nat.two_pow_pos _)
  change some (encode (mulAdd p P .infinity P (k.log2 + 1) k 0)) =
    some (Spec.encode (k • P.toSpec (3 : ZMod p)))
  rw [encode_spec hQv, hQ, infinity_toSpec, zero_nsmul, add_zero]

end Ethereum.BN254
