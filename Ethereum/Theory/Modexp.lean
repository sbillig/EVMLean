import Ethereum.PrecompiledContracts
import Ethereum.Modexp.Spec

/-!
The MODEXP precompile `Ξ_EXPMOD` in terms of the specification in `Ethereum/Modexp/Spec.lean`.
-/

namespace Ethereum

open Modexp

/-! ## Bytes -/

theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  show ByteArray.toList.loop b 0 [] = _
  suffices h : ∀ i r, ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i by
    simpa using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct (bs := b) with
  | case1 i r hlt ih =>
    rw [ByteArray.toList.loop, ite_eq_left hlt, ih, List.reverse_cons, List.append_assoc]
    congr 1
    have hi : i < b.data.size := hlt
    have hlen : i < b.data.toList.length := by rw [Array.length_toList]; exact hi
    have hget : b.get! i = b.data.toList[i]'hlen := by
      rw [Array.getElem_toList]; exact getElem!_pos b.data i hi
    rw [hget, List.singleton_append, List.getElem_cons_drop]
  | case2 i r hge =>
    rw [ByteArray.toList.loop, ite_eq_right hge]
    have : b.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt hge
    rw [List.drop_eq_nil_of_le this, List.append_nil]

theorem fromBytes'_replicate_append (k : ℕ) (l : List UInt8) :
    fromBytes' (List.replicate k 0 ++ l) = 2 ^ (8 * k) * fromBytes' l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, fromBytes', ih,
      show 8 * (k + 1) = 8 + 8 * k by ring, pow_add]
    have : (0 : UInt8).toFin.val = 0 := rfl
    rw [this]
    ring

theorem fromBE_append_zeroes (A : ByteArray) (k : ℕ) :
    fromByteArrayBigEndian (A ++ ByteArray.zeroes k) = fromByteArrayBigEndian A * 2 ^ (8 * k) := by
  simp only [fromByteArrayBigEndian, fromBytesBigEndian, Function.comp, byteArray_toList_eq,
    ByteArray.toList_data_append, ByteArray.zeroes, List.reverse_append, Array.toList_replicate,
    List.reverse_replicate]
  rw [fromBytes'_replicate_append, mul_comm]

theorem zeroes_size (k : ℕ) : (ByteArray.zeroes k).size = k := Array.size_replicate

theorem readWithoutPadding_size_le (d : ByteArray) (off w : ℕ) :
    (d.readWithoutPadding off w).size ≤ w := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · simp only [ByteArray.size_extract]; omega

/-- `nat_of_slice` is the specification's `field`. -/
theorem nat_of_slice_eq (d : ByteArray) (off w : ℕ) : nat_of_slice d off w = field d off w := by
  unfold nat_of_slice field ByteArray.readWithPadding
  rw [fromBE_append_zeroes, Nat.shiftLeft_eq]

theorem field_lt (d : ByteArray) (off w : ℕ) : field d off w < 2 ^ (8 * w) := by
  have hs : (d.readWithPadding off w).size = w := by
    unfold ByteArray.readWithPadding
    have := readWithoutPadding_size_le d off w
    rw [ByteArray.size_append, zeroes_size]
    omega
  have := fromBytes'_le (bs := (d.readWithPadding off w).toList.reverse)
  rw [List.length_reverse, byteArray_toList_eq, Array.length_toList] at this
  change fromBytes' _ < 2 ^ (8 * (d.readWithPadding off w).size) at this
  rw [hs] at this
  unfold field fromByteArrayBigEndian fromBytesBigEndian
  rw [byteArray_toList_eq]
  exact this

theorem fromBytesBigEndian_snoc (l : List UInt8) (b : UInt8) :
    fromBytesBigEndian (l ++ [b]) = fromBytesBigEndian l * 256 + b.toNat := by
  simp only [fromBytesBigEndian, Function.comp, List.reverse_append, List.reverse_singleton,
    List.singleton_append, fromBytes']
  rw [show (2 : ℕ) ^ 8 = 256 from rfl, add_comm, mul_comm]
  rfl

/-- The `n` bytes of `a`, big-endian, read back. -/
theorem fromBytesBigEndian_ofFn_shift (n a : ℕ) :
    fromBytesBigEndian (List.ofFn fun i : Fin n => (a >>> (8 * (n - 1 - i.val))).toUInt8) =
      a % 2 ^ (8 * n) := by
  induction n generalizing a with
  | zero => simp [fromBytesBigEndian, fromBytes', Nat.mod_one]
  | succ n ih =>
    rw [List.ofFn_succ_last, fromBytesBigEndian_snoc]
    have hf : (fun i : Fin n => (a >>> (8 * (n + 1 - 1 - (Fin.castSucc i).val))).toUInt8) =
        fun i : Fin n => ((a >>> 8) >>> (8 * (n - 1 - i.val))).toUInt8 := by
      funext i
      rw [← Nat.shiftRight_add]
      congr 2
      have := i.isLt
      simp only [Fin.val_castSucc]
      omega
    rw [hf, ih, Fin.val_last, show n + 1 - 1 - n = 0 by omega, Nat.mul_zero, Nat.shiftRight_zero,
      Nat.shiftRight_eq_div_pow, show 8 * (n + 1) = 8 + 8 * n by ring, pow_add, Nat.mod_mul]
    rw [Nat.toUInt8, UInt8.toNat_ofNat']
    norm_num
    ring

theorem fromBytes'_inj : ∀ {l₁ l₂ : List UInt8}, l₁.length = l₂.length →
    fromBytes' l₁ = fromBytes' l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: t₁, b₂ :: t₂, hl, h => by
    simp only [fromBytes'] at h
    have h1 := b₁.toFin.isLt
    have h2 := b₂.toFin.isLt
    change b₁.toFin.val < 256 at h1
    change b₂.toFin.val < 256 at h2
    have hb : b₁.toFin.val = b₂.toFin.val := by omega
    have ht : fromBytes' t₁ = fromBytes' t₂ := by omega
    rw [fromBytes'_inj (by simpa using hl) ht, show b₁ = b₂ from UInt8.toFin_inj.mp (Fin.ext hb)]

theorem fromBytesBigEndian_inj {l₁ l₂ : List UInt8} (hl : l₁.length = l₂.length)
    (h : fromBytesBigEndian l₁ = fromBytesBigEndian l₂) : l₁ = l₂ :=
  List.reverse_inj.mp (fromBytes'_inj (by simpa using hl) h)

theorem toBytesBE_size (n x : ℕ) : (toBytesBE n x).size = n := Array.size_ofFn

/-- `BE` zero-padded on the left to `n` bytes is the `n`-byte encoding. -/
theorem pad_BE (n x : ℕ) (hx : x < 2 ^ (8 * n)) :
    ByteArray.zeroes (n - (BE x).size) ++ BE x = toBytesBE n x := by
  have hs := BE_le hx
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.toList_data_append]
  apply fromBytesBigEndian_inj
  · simp only [ByteArray.zeroes, Array.toList_replicate, List.length_append, List.length_replicate,
      Array.length_toList]
    change n - (BE x).size + (BE x).size = (toBytesBE n x).size
    rw [toBytesBE_size]; omega
  · have e1 : (BE x).data.toList = toBytesBigEndian x := List.toList_data_toByteArray
    simp only [ByteArray.zeroes, Array.toList_replicate, e1]
    rw [show (toBytesBE n x).data.toList = List.ofFn fun i : Fin n =>
        (x >>> (8 * (n - 1 - i.val))).toUInt8 from Array.toList_ofFn, fromBytesBigEndian_ofFn_shift,
      Nat.mod_eq_of_lt hx]
    simp only [fromBytesBigEndian, toBytesBigEndian, Function.comp, List.reverse_append,
      List.reverse_reverse, List.reverse_replicate, extend_bytes_zero, fromBytes'_toBytes']

/-! ## Square-and-multiply -/

theorem mod_mul_pow_mod (x y q m : ℕ) : (x % m) * (y % m) ^ q % m = x * y ^ q % m := by
  conv_lhs => rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]

theorem expModAux_eq (m : ℕ) : ∀ n a c, expModAux m a c n = a * c ^ n % m := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a c
    cases n with
    | zero => simp [expModAux]
    | succ k =>
      have hlt : (k + 1) / 2 < k + 1 := Nat.div_lt_self (Nat.succ_pos k) (by decide)
      unfold expModAux
      split
      · rename_i h
        have h1 : (k + 1) % 2 = 1 := by simpa using h
        rw [ih _ hlt, mod_mul_pow_mod, ← pow_two, ← pow_mul, mul_assoc, ← pow_succ']
        congr 3
        omega
      · rename_i h
        have h1 : ¬ (k + 1) % 2 = 1 := by simpa using h
        rw [ih _ hlt, mod_mul_pow_mod, ← pow_two, ← pow_mul]
        congr 3
        omega

/-- **`expMod` is `b ^ n mod m`.** -/
theorem expMod_eq (m b n : ℕ) : expMod m b n = b ^ n % m := by
  rw [expMod, expModAux_eq, one_mul, ← Nat.pow_mod]

/-! ## The precompile -/

theorem gas_eq (d : ByteArray) :
    max 200
      (((max (field d 0 32) (field d 64 32) + 7) / 8) ^ 2 *
          max
            (if (decide (field d 32 32 ≤ 32) &&
                  field d (96 + field d 0 32) (field d 32 32) == 0) = true then 0
            else if field d 32 32 ≤ 32 then
              Nat.log 2 (field d (96 + field d 0 32) (field d 32 32))
            else
              8 * (field d 32 32 - 32) +
                if 32 < field d 32 32 ∧ (field d (96 + field d 0 32) 32 != 0) = true then
                  Nat.log 2 (field d (96 + field d 0 32) 32)
                else 0)
            1 / 3) = gas d := by
  simp only [gas, multiplicationComplexity, adjustedExpLength, expLength, baseLength, modLength,
    exponent]
  congr 3
  by_cases h : field d 32 32 ≤ 32 <;>
    by_cases he : field d (96 + field d 0 32) (field d 32 32) = 0 <;>
    by_cases hh : field d (96 + field d 0 32) 32 = 0 <;>
    first | (simp [h, he, hh]; done) | simp [h, he, hh, Nat.lt_of_not_le h]

theorem output_core (ml m b e : ℕ) (hmlt : m < 2 ^ (8 * ml)) :
    (if (ml == 0 || m == 0) = true then ByteArray.zeroes ml
    else
      (if ml ≥ (BE (expMod m b e)).size then ByteArray.zeroes (ml - (BE (expMod m b e)).size)
        else ByteArray.empty) ++ BE (expMod m b e)) =
      toBytesBE ml (if m = 0 then 0 else b ^ e % m) := by
  have zeroes_eq : ByteArray.zeroes ml = toBytesBE ml 0 := by
    apply ByteArray.ext
    apply Array.ext
    · simp [ByteArray.zeroes, toBytesBE]
    · intro i h1 h2
      simp [ByteArray.zeroes, toBytesBE]
  by_cases h0 : ml = 0 ∨ m = 0
  · have : (ml == 0 || m == 0) = true := by
      rcases h0 with h | h <;> simp [h]
    rw [ite_eq_left this, zeroes_eq]
    rcases h0 with h | h
    · subst h; apply ByteArray.ext; simp [toBytesBE]
    · rw [ite_eq_left h]
  · have : (ml == 0 || m == 0) = false := by simp; omega
    rw [ite_eq_right (by simp [this]), expMod_eq]
    have hr : b ^ e % m < 2 ^ (8 * ml) := lt_trans (Nat.mod_lt _ (by omega)) hmlt
    rw [ite_eq_left (BE_le hr), ite_eq_right (show ¬ m = 0 by omega), pad_BE _ _ hr]

theorem output_eq (d : ByteArray) :
    (if (field d 64 32 == 0 || field d (96 + field d 0 32 + field d 32 32) (field d 64 32) == 0) = true
      then ByteArray.zeroes (field d 64 32)
    else
      (if field d 64 32 ≥ (BE (expMod (field d (96 + field d 0 32 + field d 32 32) (field d 64 32))
            (field d 96 (field d 0 32)) (field d (96 + field d 0 32) (field d 32 32)))).size then
          ByteArray.zeroes (field d 64 32 - (BE (expMod (field d (96 + field d 0 32 + field d 32 32)
            (field d 64 32)) (field d 96 (field d 0 32))
            (field d (96 + field d 0 32) (field d 32 32)))).size)
        else ByteArray.empty) ++
      BE (expMod (field d (96 + field d 0 32 + field d 32 32) (field d 64 32))
        (field d 96 (field d 0 32)) (field d (96 + field d 0 32) (field d 32 32)))) = output d :=
  output_core _ _ _ _ (field_lt _ _ _)

/-- MODEXP before Osaka: EIP-198's output at EIP-2565's price, with no bound on the lengths. -/
theorem Ξ_EXPMOD_eq (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hfork : I.header.fork = .Cancun) :
    Ξ_EXPMOD σ g A I =
      if g.toNat < gas I.calldata then (∅, ⟨0⟩, A, .empty)
      else (σ, g - .ofNat (gas I.calldata), A, output I.calldata) := by
  simp only [Ξ_EXPMOD, nat_of_slice_eq, hfork, reduceCtorEq, false_and, ↓reduceIte]
  rw [gas_eq, output_eq]


theorem gasOsaka_eq (d : ByteArray) :
    max 500
      ((if 32 < max (field d 0 32) (field d 64 32) then
          2 * ((max (field d 0 32) (field d 64 32) + 7) / 8) ^ 2
        else 16) *
        max
          (if (decide (field d 32 32 ≤ 32) &&
                field d (96 + field d 0 32) (field d 32 32) == 0) = true then 0
          else if field d 32 32 ≤ 32 then
            Nat.log 2 (field d (96 + field d 0 32) (field d 32 32))
          else
            16 * (field d 32 32 - 32) +
              if (field d (96 + field d 0 32) 32 != 0) = true then
                Nat.log 2 (field d (96 + field d 0 32) 32)
              else 0)
          1) = gasOsaka d := by
  simp only [gasOsaka, multiplicationComplexityOsaka, adjustedExpLengthOsaka, expLength,
    baseLength, modLength, exponent]
  congr 2
  by_cases h : field d 32 32 ≤ 32 <;>
    by_cases he : field d (96 + field d 0 32) (field d 32 32) = 0 <;>
    by_cases hh : field d (96 + field d 0 32) 32 = 0 <;>
    simp [h, he, hh]

/-- MODEXP from Osaka: a length above 1,024 bytes fails (EIP-7823); otherwise EIP-198's output at
EIP-7883's price. -/
theorem Ξ_EXPMOD_eq_osaka (σ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv)
    (hfork : I.header.fork = .Osaka) :
    Ξ_EXPMOD σ g A I =
      if ¬ lengthsBounded I.calldata ∨ g.toNat < gasOsaka I.calldata then (∅, ⟨0⟩, A, .empty)
      else (σ, g - .ofNat (gasOsaka I.calldata), A, output I.calldata) := by
  simp only [Ξ_EXPMOD, nat_of_slice_eq, hfork, true_and, ↓reduceIte]
  rw [gasOsaka_eq, output_eq]
  by_cases hb : lengthsBounded I.calldata
  · have : ¬ (1024 < field I.calldata 0 32 ∨ 1024 < field I.calldata 32 32 ∨
        1024 < field I.calldata 64 32) := by
      unfold lengthsBounded baseLength expLength modLength at hb; omega
    simp only [this, hb, not_true_eq_false, false_or, ↓reduceIte]
  · have : 1024 < field I.calldata 0 32 ∨ 1024 < field I.calldata 32 32 ∨
        1024 < field I.calldata 64 32 := by
      unfold lengthsBounded baseLength expLength modLength at hb; omega
    simp only [this, hb, not_false_eq_true, true_or, ↓reduceIte]

/-- At Osaka every length of a call that succeeds is at most 1,024 bytes. -/
theorem lengthsBounded_of_Ξ_EXPMOD_osaka {σ : AccountMap} {g : UInt256} {A : Substate}
    {I : ExecutionEnv} (hfork : I.header.fork = .Osaka) (hσ : (Ξ_EXPMOD σ g A I).1 ≠ ∅) :
    lengthsBounded I.calldata := by
  rw [Ξ_EXPMOD_eq_osaka σ g A I hfork] at hσ
  by_contra hb
  simp [hb] at hσ

end Ethereum
