import Ethereum.Weierstrass.Curve
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
The order of the group of points of a short Weierstrass curve `y² = x³ + b` over
`ZMod q`, for a prime `q > 3`.

The points are finite (`coords?` embeds them in `Option (ZMod q × ZMod q)`), and at most
`2 q + 1`: an abscissa has at most two ordinates, `y` and `-y` (`card_le`). So if a prime
`r` with `2 q + 1 < 3 r` is the order of a point and `x³ + b` has no root (no point has
`y = 0`, so none has order two), the group has exactly `r` elements (`card_eq`): `r`
divides the order by Lagrange, and `2 r` would give a point of order two by Cauchy. Then
the group is cyclic, `r` kills every point, and every point is a multiple of the given one
(`nsmul_card`, `exists_nsmul_eq`, `mod_nsmul`).
-/

namespace Ethereum.Weierstrass

open WeierstrassCurve WeierstrassCurve.Affine

variable {q : ℕ} [Fact q.Prime] {b : ZMod q}

/-- The coordinates of a point: `none` for the point at infinity. -/
def coords? : (short q b).toAffine.Point → Option (ZMod q × ZMod q)
  | .zero => none
  | .some x y _ => some (x, y)

omit [Fact q.Prime] in
theorem coords?_injective : Function.Injective (coords? (q := q) (b := b)) := by
  intro P Q h
  rcases P with _ | ⟨x, y, hP⟩ <;> rcases Q with _ | ⟨x', y', hQ⟩ <;> simp_all [coords?]

instance : Finite (short q b).toAffine.Point := Finite.of_injective _ coords?_injective

/-- Whether a value lies in the lower half of `ZMod q`: of `y` and `-y ≠ y`, exactly one does. -/
def low (y : ZMod q) : Bool := decide (y.val ≤ (q - 1) / 2)

theorem low_neg (hq : 2 < q) {y : ZMod q} (hy : y ≠ 0) : low (-y) ≠ low y := by
  have hodd : q % 2 = 1 := ((Fact.out : q.Prime).eq_two_or_odd).resolve_left (by omega)
  have hlt := ZMod.val_lt y
  have hv : y.val ≠ 0 := by rwa [ne_eq, ZMod.val_eq_zero]
  rw [low, low, ZMod.neg_val, if_neg hy]
  by_cases h : y.val ≤ (q - 1) / 2 <;> simp [h] <;> omega

/-- A point as an abscissa and the half its ordinate is in. -/
def code : (short q b).toAffine.Point → Option (ZMod q × Bool)
  | .zero => none
  | .some x y _ => some (x, low y)

theorem code_injective (hq : 3 < q) (hb : b ≠ 0) : Function.Injective (code (b := b)) := by
  intro P Q h
  rcases P with _ | ⟨x, y, hP⟩ <;> rcases Q with _ | ⟨x', y', hQ⟩
  · rfl
  · simp [code] at h
  · simp [code] at h
  · simp only [code, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hl⟩ := h
    have e1 := (nonsingular_iff hq hb _ _).mp hP
    have e2 := (nonsingular_iff hq hb _ _).mp hQ
    have : (y - y') * (y + y') = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp this with h | h
    · obtain rfl : y = y' := sub_eq_zero.mp h
      rfl
    · have hy : y = -y' := eq_neg_of_add_eq_zero_left h
      by_cases h0 : y' = 0
      · subst h0; obtain rfl : y = 0 := by simpa using hy
        rfl
      · exact absurd (hy ▸ hl) (low_neg (by omega) h0)

/-- At most `2 q + 1` points: infinity, and two ordinates for each abscissa. -/
theorem card_le (hq : 3 < q) (hb : b ≠ 0) : Nat.card (short q b).toAffine.Point ≤ 2 * q + 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have := Nat.card_le_card_of_injective _ (code_injective (b := b) hq hb)
  rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option, Fintype.card_prod,
    ZMod.card, Fintype.card_bool] at this
  omega

/-- When `x³ + b` has no root, no point but `0` has `2 • P = 0`. -/
theorem eq_zero_of_two_nsmul (hq : 3 < q) (hb : b ≠ 0) (hroot : ∀ x : ZMod q, x ^ 3 + b ≠ 0)
    {P : (short q b).toAffine.Point} (hP : 2 • P = 0) : P = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  exfalso
  have hneg : Point.some x y h = -Point.some x y h :=
    eq_neg_of_add_eq_zero_left (by rwa [two_nsmul] at hP)
  rw [Point.neg_some, Point.some.injEq] at hneg
  have h2 : (2 : ZMod q) ≠ 0 := mod_cast natCast_ne_zero (k := 2) (by norm_num) (by omega)
  have hy : y = 0 := by
    have : 2 * y = 0 := by
      have := hneg.2
      simp only [negY, short] at this
      linear_combination this
    exact (mul_eq_zero.mp this).resolve_left h2
  have := (nonsingular_iff hq hb _ _).mp h
  rw [hy] at this
  exact hroot x (by linear_combination -this)

/-- **The order**: a point of prime order `r` with `2 q + 1 < 3 r`, on a curve where `x³ + b`
has no root, makes the group of order `r`. -/
theorem card_eq (hq : 3 < q) (hb : b ≠ 0) (hroot : ∀ x : ZMod q, x ^ 3 + b ≠ 0) {r : ℕ}
    (hr : r.Prime) (hbound : 2 * q + 1 < 3 * r) {G : (short q b).toAffine.Point} (hG : G ≠ 0)
    (hrG : r • G = 0) : Nat.card (short q b).toAffine.Point = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hord : addOrderOf G = r := addOrderOf_eq_prime hrG hG
  obtain ⟨m, hm⟩ := hord ▸ addOrderOf_dvd_natCard G
  have hpos : 0 < Nat.card (short q b).toAffine.Point := Nat.card_pos
  have hle := card_le (b := b) hq hb
  have hm12 : m = 1 ∨ m = 2 := by
    have : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, Nat.mul_zero] at hm; omega
      · exact h
    have : m < 3 := by
      by_contra h
      have : r * 3 ≤ r * m := Nat.mul_le_mul_left _ (by omega)
      omega
    omega
  rcases hm12 with rfl | rfl
  · simpa using hm
  · exfalso
    haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' (G := (short q b).toAffine.Point) 2
      (by rw [hm]; exact dvd_mul_left _ _)
    have h0 := eq_zero_of_two_nsmul hq hb hroot (P := P) (by rw [← hP]; exact addOrderOf_nsmul_eq_zero P)
    rw [h0, addOrderOf_zero] at hP
    omega

section Prime

variable {r : ℕ} (hr : r.Prime) (hcard : Nat.card (short q b).toAffine.Point = r)
include hr hcard

/-- The group of prime order is cyclic. -/
theorem isAddCyclic_of_card : IsAddCyclic (short q b).toAffine.Point :=
  haveI : Fact r.Prime := ⟨hr⟩
  isAddCyclic_of_prime_card hcard

omit hr in
/-- `r` kills every point. -/
theorem nsmul_card (P : (short q b).toAffine.Point) : r • P = 0 := hcard ▸ card_nsmul_eq_zero'

omit hr in
/-- Multiples depend only on the scalar modulo `r`. -/
theorem mod_nsmul (k : ℕ) (P : (short q b).toAffine.Point) : (k % r) • P = k • P := by
  conv_rhs => rw [← Nat.mod_add_div k r, add_nsmul, mul_nsmul, nsmul_card hcard, nsmul_zero,
    add_zero]

/-- Every point is a multiple of any point but `0`. -/
theorem exists_nsmul_eq {G : (short q b).toAffine.Point} (hG : G ≠ 0)
    (P : (short q b).toAffine.Point) : ∃ k < r, k • G = P := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hord : addOrderOf G = r := addOrderOf_eq_prime (nsmul_card hcard G) hG
  have htop : AddSubgroup.zmultiples G = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, hord, hcard])
  have hmem : P ∈ AddSubgroup.zmultiples G := htop ▸ AddSubgroup.mem_top P
  rw [← (isOfFinAddOrder_of_finite G).mem_multiples_iff_mem_zmultiples] at hmem
  obtain ⟨k, rfl⟩ := hmem
  exact ⟨k % r, Nat.mod_lt _ hr.pos, mod_nsmul hcard k G⟩

end Prime

/-! ## The endomorphism `(x, y) ↦ (β x, y)` -/

section Endo

variable {β : ZMod q} (hq : 3 < q) (hb : b ≠ 0) (hβ : β ^ 3 = 1)
include hq hb hβ

theorem phi_nonsingular {x y : ZMod q} (h : (short q b).toAffine.Nonsingular x y) :
    (short q b).toAffine.Nonsingular (β * x) y := by
  rw [nonsingular_iff hq hb] at h ⊢
  rw [h]; linear_combination (-x ^ 3) * hβ

/-- `(x, y) ↦ (β x, y)` on points, for `β ^ 3 = 1`. -/
def phi : (short q b).toAffine.Point → (short q b).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (β * x) y (phi_nonsingular hq hb hβ h)

omit hq hb in
theorem beta_ne_zero : β ≠ 0 := by
  rintro rfl; simp at hβ

omit hq hb in
theorem slope_phi (x₁ x₂ y₁ y₂ : ZMod q) :
    (short q b).toAffine.slope (β * x₁) (β * x₂) y₁ y₂ =
      β ^ 2 * (short q b).toAffine.slope x₁ x₂ y₁ y₂ := by
  have hβ0 := beta_ne_zero hβ
  have hx : β * x₁ = β * x₂ ↔ x₁ = x₂ := mul_right_inj' hβ0
  unfold slope
  by_cases h1 : x₁ = x₂
  · rw [if_pos (hx.mpr h1), if_pos h1]
    by_cases h2 : y₁ = (short q b).toAffine.negY (β * x₂) y₂
    · have h2' : y₁ = (short q b).toAffine.negY x₂ y₂ := by simpa [negY, short] using h2
      rw [if_pos h2, if_pos h2', mul_zero]
    · have h2' : ¬ y₁ = (short q b).toAffine.negY x₂ y₂ := by simpa [negY, short] using h2
      rw [if_neg h2, if_neg h2']
      simp only [negY, short]
      ring
  · rw [if_neg (fun h => h1 (hx.mp h)), if_neg h1]
    have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    linear_combination -(y₁ - y₂) * hβ

theorem phi_add (P Q : (short q b).toAffine.Point) :
    phi hq hb hβ (P + Q) = phi hq hb hβ P + phi hq hb hβ Q := by
  have hβ0 := beta_ne_zero hβ
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · simp [phi]; rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · simp [phi]; rfl
  have hn : ∀ x y : ZMod q, (short q b).toAffine.negY x y = -y := by
    intro x y; simp [negY, short]
  by_cases hxy : x₁ = x₂ ∧ y₁ = (short q b).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    simp only [phi]
    rw [Point.add_of_Y_eq (by rw [hxy.1]) (by rw [hn, hxy.2, hn])]
    rfl
  · have hxy' : ¬ (β * x₁ = β * x₂ ∧ y₁ = (short q b).toAffine.negY (β * x₂) y₂) := by
      rintro ⟨e1, e2⟩
      exact hxy ⟨mul_left_cancel₀ hβ0 e1, by rw [e2, hn, hn]⟩
    rw [Point.add_some hxy]
    simp only [phi]
    rw [Point.add_some hxy', Point.some.injEq, slope_phi hβ]
    generalize (short q b).toAffine.slope x₁ x₂ y₁ y₂ = ℓ
    constructor
    · simp only [addX, short]
      linear_combination -ℓ ^ 2 * β * hβ
    · simp only [addY, negAddY, addX, negY, short]
      linear_combination (ℓ ^ 3 * (β ^ 3 + 1) - 2 * ℓ * x₁ - ℓ * x₂) * hβ

/-- `phi` as an additive map. -/
def phiHom : (short q b).toAffine.Point →+ (short q b).toAffine.Point where
  toFun := phi hq hb hβ
  map_zero' := rfl
  map_add' := phi_add hq hb hβ

/-- On a group of prime order `r` generated by `G`, `phi` is multiplication by `l` once it is at
`G`. -/
theorem phi_eq_nsmul {r : ℕ} (hr : r.Prime) (hcard : Nat.card (short q b).toAffine.Point = r)
    {G : (short q b).toAffine.Point} (hG : G ≠ 0) {l : ℕ} (hl : phi hq hb hβ G = l • G)
    (P : (short q b).toAffine.Point) : phi hq hb hβ P = l • P := by
  obtain ⟨k, -, rfl⟩ := exists_nsmul_eq hr hcard hG P
  have := map_nsmul (phiHom hq hb hβ) k G
  change phi hq hb hβ (k • G) = k • phi hq hb hβ G at this
  rw [this, hl, ← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

end Endo

end Ethereum.Weierstrass
