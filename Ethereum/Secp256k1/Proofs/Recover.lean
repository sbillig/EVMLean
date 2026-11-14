import Ethereum.Secp256k1.Proofs.MulAdd

/-!
`Ethereum.Secp256k1.recover` computes `Spec.recover`, for all inputs.

The proof composes the layers below it: the square root and parity choice of
`Impl.liftX` against `Spec.liftX`, `Impl.mulAdd` against `•`, and the final
conversion to affine coordinates against Mathlib's `toAffine`.
-/

namespace Ethereum.Secp256k1

open Spec WeierstrassCurve WeierstrassCurve.Jacobian Impl

/-! ## Square roots and parities in `ZMod p` -/

private theorem p_odd : p % 2 = 1 := by decide

/-- A nonzero element and its negative have different parities, `p` being odd. -/
theorem val_neg_mod_two {y : ZMod p} (hy : y ≠ 0) : (-y).val % 2 ≠ y.val % 2 := by
  rw [ZMod.neg_val, if_neg hy]
  have := ZMod.val_lt y
  have := p_odd
  omega

/-- Two square roots of the same number with the same parity are equal. -/
theorem eq_of_sq_eq {y₁ y₂ : ZMod p} (h : y₁ ^ 2 = y₂ ^ 2)
    (hv : y₁.val % 2 = y₂.val % 2) :
    y₁ = y₂ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact h
  · by_cases hy : y₂ = 0
    · rw [h, hy, neg_zero]
    · exact absurd (h ▸ hv) (val_neg_mod_two hy)

/-- Euler's criterion for `p ≡ 3 (mod 4)`: if `a` is a square, `a ^ ((p + 1) / 4)` is a
square root of it. -/
theorem sq_pow_of_isSquare {a y : ZMod p} (hy : y ^ 2 = a) : (a ^ ((p + 1) / 4)) ^ 2 = a := by
  by_cases ha : a = 0
  · rw [ha, zero_pow (by decide), zero_pow two_ne_zero]
  · have hy0 : y ≠ 0 := by rintro rfl; exact ha (by rw [← hy]; ring)
    rw [← pow_mul, show (p + 1) / 4 * 2 = (p - 1) / 2 + 1 by decide, pow_succ, ← hy,
      ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by decide, ZMod.pow_card_sub_one_eq_one hy0,
      one_mul]

/-! ## Lifting an abscissa -/

private theorem coords_affine (x y : ℕ) :
    (⟨x, y, 1⟩ : Impl.Point).coords = ![(x : ZMod p), (y : ZMod p), 1] := by
  simp [Impl.Point.coords]

/-- An affine point with integer coordinates satisfying the equation. -/
theorem affine_valid {x y : ℕ} (h : (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + 7) :
    (⟨x, y, 1⟩ : Impl.Point).Valid := by
  rw [Impl.Point.Valid, coords_affine, nonsingular_some]
  exact (Spec.nonsingular_iff _ _).mpr h

theorem affine_toSpec {x y : ℕ} (h : (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + 7) :
    (⟨x, y, 1⟩ : Impl.Point).toSpec = .some _ _ ((Spec.nonsingular_iff _ _).mpr h) := by
  have hv := affine_valid h
  rw [Impl.Point.Valid, coords_affine] at hv
  rw [Impl.Point.toSpec, coords_affine, Jacobian.Point.toAffine_some hv]

theorem liftX_spec {x v : ℕ} :
    (∀ R ∈ Impl.liftX x v, R.Valid) ∧
      (Impl.liftX x v).map Impl.Point.toSpec = Spec.liftX x v := by
  have hval : ∀ {a : ℕ}, a < p → (a : ZMod p).val = a := ZMod.val_cast_of_lt
  simp only [Impl.liftX, Spec.liftX]
  generalize hαdef : fadd (fmul (fmul x x) x) 7 = α
  have hα : (α : ZMod p) = (x : ZMod p) ^ 3 + 7 := by
    rw [← hαdef]
    simp only [natCast_fadd, natCast_fmul, Nat.cast_ofNat]
    ring
  have hαp : α < p := hαdef ▸ fadd_lt _ _
  generalize hβdef : powMod α ((p + 1) / 4) p = β
  have hβp : β < p := by
    rw [← hβdef, powMod_eq]
    exact Nat.mod_lt _ p_pos
  generalize hy : (if β % 2 = v then β else (p - β) % p) = y
  have hyp : y < p := by
    rw [← hy]
    split_ifs
    · exact hβp
    · exact Nat.mod_lt _ p_pos
  -- `y` is `β` or `-β`.
  have hyβ : (y : ZMod p) = β ∨ (y : ZMod p) = -β := by
    rw [← hy]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (by rw [ZMod.natCast_mod, Nat.cast_sub hβp.le, ZMod.natCast_self, zero_sub])
  have hysq : (y : ZMod p) ^ 2 = (β : ZMod p) ^ 2 := by
    rcases hyβ with h | h <;> rw [h]
    ring
  -- If `y` has the wrong parity, so do `β` and `-β`.
  have hpar : y % 2 ≠ v → ∀ c : ZMod p, c ^ 2 = (β : ZMod p) ^ 2 → c.val % 2 ≠ v := by
    intro hyv c hc hcv
    have hβv : β % 2 ≠ v := fun h => hyv (by rw [← hy, if_pos h]; exact h)
    have hy' : y = (p - β) % p := by rw [← hy, if_neg hβv]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with rfl | rfl
    · exact hβv (by rwa [hval hβp] at hcv)
    · by_cases hβ0 : β = 0
      · rw [hβ0, Nat.cast_zero, neg_zero, ZMod.val_zero, Nat.zero_mod] at hcv
        exact hyv (by rw [hy', hβ0, Nat.sub_zero, Nat.mod_self]; exact hcv)
      · have hne : (β : ZMod p) ≠ 0 := by
          rwa [ne_eq, ← Nat.cast_zero, natCast_inj hβp p_pos]
        rw [ZMod.neg_val, if_neg hne, hval hβp] at hcv
        exact hyv (by rw [hy', Nat.mod_eq_of_lt (a := p - β) (b := p) (by omega)]; exact hcv)
  split_ifs with hc hex hex
  -- `y` is a root of parity `v`: both sides are the point `(x, y)`.
  · have hyα : (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + 7 := by
      rw [← hα, ← hc.1, natCast_fmul]
      ring
    obtain ⟨hcx, hcv⟩ := hex.choose_spec
    rw [Spec.nonsingular_iff] at hcx
    have hcy : hex.choose = y :=
      eq_of_sq_eq (hcx.trans hyα.symm) (by rw [hcv, hval hyp, hc.2])
    refine ⟨fun R hR => ?_, ?_⟩
    · obtain rfl := Option.some.inj hR
      exact affine_valid hyα
    · rw [Option.map_some, affine_toSpec hyα]
      simp only [Option.some.injEq, Affine.Point.some.injEq, true_and]
      exact hcy.symm
  -- `y` is a root of parity `v`, so some root of parity `v` exists.
  · exfalso
    have hyα : (y : ZMod p) ^ 2 = (x : ZMod p) ^ 3 + 7 := by
      rw [← hα, ← hc.1, natCast_fmul]
      ring
    exact hex ⟨y, (Spec.nonsingular_iff _ _).mpr hyα, by rw [hval hyp, hc.2]⟩
  -- `y` is no root of parity `v`, but some root of parity `v` exists.
  · exfalso
    obtain ⟨c, hcx, hcv⟩ := hex
    rw [Spec.nonsingular_iff, ← hα] at hcx
    have hβsq : (β : ZMod p) ^ 2 = α := by
      rw [← hβdef, natCast_powMod]
      exact sq_pow_of_isSquare hcx
    have hyy : fmul y y = α :=
      (natCast_inj (fmul_lt _ _) hαp).mp (by rw [natCast_fmul, ← pow_two, hysq, hβsq])
    exact hpar (fun h => hc ⟨hyy, h⟩) c (hcx.trans hβsq.symm) hcv
  · exact ⟨fun _ h => (nomatch h), rfl⟩

/-! ## The negated generator -/

private theorem gy_le : gy ≤ p := by decide

private theorem negG_sq : ((p - gy : ℕ) : ZMod p) ^ 2 = (gx : ZMod p) ^ 3 + 7 := by
  rw [Nat.cast_sub gy_le, ZMod.natCast_self, zero_sub, neg_sq]
  exact (Spec.nonsingular_iff _ _).mp G_nonsingular

theorem negG_toSpec : (⟨gx, p - gy, 1⟩ : Impl.Point).toSpec = -G := by
  rw [affine_toSpec negG_sq, G, Affine.Point.neg_some, Affine.Point.some.injEq]
  simp [Nat.cast_sub gy_le, WeierstrassCurve.Affine.negY]

/-! ## Affine coordinates of the result -/

theorem toAffine_spec {P : Impl.Point} (hP : P.Valid) :
    P.toAffine = (match P.toSpec with
      | .zero => none
      | .some x y _ => some (x, y)).map fun q : ZMod p × ZMod p => (q.1.val, q.2.val) := by
  unfold Impl.Point.toAffine
  split_ifs with hz
  · rw [Impl.Point.toSpec, Jacobian.Point.toAffine_of_Z_eq_zero (natCast_eq_zero_iff_mod.mpr hz)]
    rfl
  · have hz' : P.coords 2 ≠ 0 := fun h => hz (natCast_eq_zero_iff_mod.mp h)
    rw [Impl.Point.toSpec, Jacobian.Point.toAffine_of_Z_ne_zero hP hz']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [← ZMod.val_cast_of_lt (fmul_lt _ _)]
      refine congrArg ZMod.val ?_
      rw [natCast_fmul, natCast_fmul, natCast_finv, coords_zero, coords_two]
      ring
    · rw [← ZMod.val_cast_of_lt (fmul_lt _ _)]
      refine congrArg ZMod.val ?_
      rw [natCast_fmul, natCast_fmul, natCast_fmul, natCast_finv, coords_one, coords_two]
      ring

/-! ## Recovery -/

/-- The scalar `r⁻¹ t` modulo `n`, as `recover` computes it. -/
private theorem scalar_eq (r t : ℕ) :
    ((r : ZMod n)⁻¹ * t).val = powMod r (n - 2) n * t % n := by
  rw [← pow_sub_two_eq_inv two_lt_n, ← natCast_powMod, ← Nat.cast_mul, ZMod.val_natCast]

/-- The implementation of secp256k1 public-key recovery computes its specification. -/
theorem recover_eq (e v r s : ℕ) :
    recover e v r s = (Spec.recover e v r s).map fun q => (q.1.val, q.2.val) := by
  unfold recover Spec.recover
  split_ifs with h
  swap
  · rfl
  obtain ⟨hr0, hrn, -, -, -⟩ := h
  obtain ⟨hvalid, hspec⟩ := liftX_spec (x := r) (v := v)
  rcases hR : Impl.liftX r v with _ | R
  · rw [hR, Option.map_none] at hspec
    rw [← hspec]
    rfl
  · rw [hR, Option.map_some] at hspec
    rw [← hspec]
    have hRv : R.Valid := hvalid R (by rw [hR]; rfl)
    have hGv : (⟨gx, p - gy, 1⟩ : Impl.Point).Valid := affine_valid negG_sq
    have hlt : ∀ t, powMod r (n - 2) n * t % n < 2 ^ 256 :=
      fun t => (Nat.mod_lt _ (by decide)).trans (by decide)
    obtain ⟨hQv, hQ⟩ := mulAdd_spec hRv hGv (hRv.add hGv) (toSpec_add hRv hGv) 256 _ _
      (hlt s) (hlt e)
    simp only
    rw [toAffine_spec hQv, hQ, negG_toSpec, neg_nsmul, ← sub_eq_add_neg, ← scalar_eq,
      ← scalar_eq]
    rfl

/-! ## The order of the generator -/

private theorem G_sq : (gy : ZMod p) ^ 2 = (gx : ZMod p) ^ 3 + 7 :=
  (Spec.nonsingular_iff _ _).mp G_nonsingular

theorem G_toSpec : (⟨gx, gy, 1⟩ : Impl.Point).toSpec = G := affine_toSpec G_sq

/-- `n • G = 0`, by evaluating `n • G` with `Impl.mulAdd` in the kernel. `Spec.recover`
does not use this; it lets `(n - u) • G` stand for `-(u • G)`. -/
theorem nsmul_G : n • G = 0 := by
  have hG := affine_valid G_sq
  obtain ⟨-, h⟩ := mulAdd_spec hG infinity_valid hG
    (by rw [infinity_toSpec, add_zero]) 256 n 0 (by decide) (by decide)
  have hz : (mulAdd ⟨gx, gy, 1⟩ .infinity ⟨gx, gy, 1⟩ 256 n 0).z % p = 0 := by
    decide +kernel
  generalize mulAdd ⟨gx, gy, 1⟩ .infinity ⟨gx, gy, 1⟩ 256 n 0 = Q at h hz
  have hQz : Q.coords 2 = 0 := natCast_eq_zero_iff_mod.mpr hz
  rw [infinity_toSpec, zero_nsmul, add_zero, G_toSpec, Impl.Point.toSpec,
    Jacobian.Point.toAffine_of_Z_eq_zero hQz] at h
  exact h.symm

end Ethereum.Secp256k1
