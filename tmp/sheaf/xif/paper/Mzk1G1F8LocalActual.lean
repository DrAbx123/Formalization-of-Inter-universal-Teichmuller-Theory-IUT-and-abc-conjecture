import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic

/-! # F8 local estimates (route §8.6 L838-848)

This file starts the *unconditional* local part of F8: for a point of the Fermat
curve `X^n + Y^n = Z^n` over a field with an absolute value, the local height of
the `Y`-coordinate is controlled by those of `X` and `Z`, with factor `1` in the
nonarchimedean case and factor `2` in the archimedean case.  These are exactly the
pointwise estimates used in route L846-848; no general height functoriality is
used.
-/


noncomputable section

namespace LeanFormal.IUT.XiFPaper.F8LocalActual

variable {K : Type*} [Field K]

/-- Nonarchimedean triangle inequality for a difference. -/
lemma nonarch_sub_le_max {v : AbsoluteValue K ℝ}
    (hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y)) (a b : K) :
    v (a - b) ≤ max (v a) (v b) := by
  have h := hna a (-b)
  simpa [sub_eq_add_neg] using h

/-- Archimedean triangle inequality with the explicit factor `2`. -/
lemma arch_sub_le_two_max {v : AbsoluteValue K ℝ} (a b : K) :
    v (a - b) ≤ 2 * max (v a) (v b) := by
  have h := AbsoluteValue.sub_le_add v a b
  have h2 : v a + v b ≤ 2 * max (v a) (v b) := by
    have ha : v a ≤ max (v a) (v b) := le_max_left _ _
    have hb : v b ≤ max (v a) (v b) := le_max_right _ _
    linarith
  linarith

/-- F8 local nonarchimedean estimate (route L846-848): for `X^n + Y^n = Z^n`,
`|Y| <= max |X| |Z|`. -/
lemma fermat_local_nonarch {v : AbsoluteValue K ℝ}
    (hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y)) {n : ℕ} (hn : n ≠ 0)
    {x y z : K} (h : x ^ n + y ^ n = z ^ n) :
    v y ≤ max (v x) (v z) := by
  have hy : y ^ n = z ^ n - x ^ n := by
    rw [← h]; ring
  have h1 : v (y ^ n) ≤ max (v (x ^ n)) (v (z ^ n)) := by
    rw [hy]
    simpa [max_comm] using nonarch_sub_le_max (v := v) hna (z ^ n) (x ^ n)
  simp only [AbsoluteValue.map_pow] at h1
  have hM0 : 0 ≤ max (v x) (v z) := le_trans (AbsoluteValue.nonneg v x) (le_max_left _ _)
  have h3 : max (v x ^ n) (v z ^ n) ≤ (max (v x) (v z)) ^ n := by
    refine max_le ?_ ?_
    · exact pow_le_pow_left₀ (AbsoluteValue.nonneg v x) (le_max_left _ _) _
    · exact pow_le_pow_left₀ (AbsoluteValue.nonneg v z) (le_max_right _ _) _
  exact le_of_pow_le_pow_left₀ hn hM0 (le_trans h1 h3)

/-- F8 local archimedean estimate (route L846-848, factor 2): for `X^n + Y^n = Z^n`,
`|Y| <= 2 * max |X| |Z|`. -/
lemma fermat_local_arch {v : AbsoluteValue K ℝ} {n : ℕ} (hn : 1 ≤ n)
    {x y z : K} (h : x ^ n + y ^ n = z ^ n) :
    v y ≤ 2 * max (v x) (v z) := by
  have hy : y ^ n = z ^ n - x ^ n := by
    rw [← h]; ring
  have h1 : v (y ^ n) ≤ 2 * max (v (x ^ n)) (v (z ^ n)) := by
    rw [hy]
    simpa [max_comm] using arch_sub_le_two_max (v := v) (z ^ n) (x ^ n)
  simp only [AbsoluteValue.map_pow] at h1
  have hM0 : 0 ≤ max (v x) (v z) := le_trans (AbsoluteValue.nonneg v x) (le_max_left _ _)
  have h3 : max (v x ^ n) (v z ^ n) ≤ (max (v x) (v z)) ^ n := by
    refine max_le ?_ ?_
    · exact pow_le_pow_left₀ (AbsoluteValue.nonneg v x) (le_max_left _ _) _
    · exact pow_le_pow_left₀ (AbsoluteValue.nonneg v z) (le_max_right _ _) _
  have h2n : (2 : ℝ) ≤ 2 ^ n := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    simpa using this
  have hMnn : 0 ≤ (max (v x) (v z)) ^ n := pow_nonneg hM0 _
  have h2 : 2 * max (v x ^ n) (v z ^ n) ≤ (2 * max (v x) (v z)) ^ n := by
    rw [mul_pow]
    exact mul_le_mul h2n h3
      (le_trans (pow_nonneg (AbsoluteValue.nonneg v x) n) (le_max_left _ _))
      (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)
  have hbase : 0 ≤ 2 * max (v x) (v z) := by positivity
  exact le_of_pow_le_pow_left₀ (Nat.ne_of_gt hn) hbase (le_trans h1 h2)

#print axioms nonarch_sub_le_max
#print axioms arch_sub_le_two_max
#print axioms fermat_local_nonarch
#print axioms fermat_local_arch

variable [NumberField K]

/-! ## Height comparison from pointwise estimates (route L846-848) -/

/-- If `u` is bounded by `w` at every nonarchimedean place and by `2*w` at every
archimedean place, then the multiplicative heights satisfy
`mulHeight u <= 2^finrank * mulHeight w`.  This is the explicit `O(log 2)` used in
F8 (route L846-848). -/
lemma mulHeight_le_of_arch_two {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (u : ι → K) (w : ι' → K) (hu : u ≠ 0) (hw : w ≠ 0)
    (hnonarch : ∀ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      (⨆ i : ι, v.val (u i)) ≤ ⨆ j : ι', v.val (w j))
    (harch : ∀ v : NumberField.InfinitePlace K,
      (⨆ i : ι, v (u i)) ≤ 2 * ⨆ j : ι', v (w j)) :
    Height.mulHeight u ≤ (2 : ℝ) ^ Module.finrank ℚ K * Height.mulHeight w := by
  rw [Height.mulHeight_eq hu, Height.mulHeight_eq hw]
  rw [NumberField.prod_archAbsVal_eq, NumberField.prod_archAbsVal_eq]
  have harch_nonneg_u : ∀ v : NumberField.InfinitePlace K,
      0 ≤ (⨆ i, v (u i)) := fun v => Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v.1 _)
  have harch_nonneg_w : ∀ v : NumberField.InfinitePlace K,
      0 ≤ (⨆ i, v (w i)) := fun v => Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v.1 _)
  have harch_prod : (∏ v : NumberField.InfinitePlace K, (⨆ i, v (u i)) ^ v.mult)
      ≤ (2 : ℝ) ^ Module.finrank ℚ K
        * ∏ v : NumberField.InfinitePlace K, (⨆ i, v (w i)) ^ v.mult := by
    calc (∏ v : NumberField.InfinitePlace K, (⨆ i, v (u i)) ^ v.mult)
        ≤ ∏ v : NumberField.InfinitePlace K, (2 * ⨆ i, v (w i)) ^ v.mult := by
            refine Finset.prod_le_prod (fun v _ => pow_nonneg (harch_nonneg_u v) _) ?_
            intro v _
            exact pow_le_pow_left₀ (harch_nonneg_u v) (harch v) _
      _ = ∏ v : NumberField.InfinitePlace K,
            ((2 : ℝ) ^ v.mult * (⨆ i, v (w i)) ^ v.mult) := by
            refine Finset.prod_congr rfl ?_
            intro v _; rw [mul_pow]
      _ = (∏ v : NumberField.InfinitePlace K, (2 : ℝ) ^ v.mult)
            * ∏ v : NumberField.InfinitePlace K, (⨆ i, v (w i)) ^ v.mult :=
            Finset.prod_mul_distrib
      _ = (2 : ℝ) ^ Module.finrank ℚ K
            * ∏ v : NumberField.InfinitePlace K, (⨆ i, v (w i)) ^ v.mult := by
            rw [Finset.prod_pow_eq_pow_sum, ← NumberField.totalWeight_eq_sum_mult,
              NumberField.totalWeight_eq_finrank]
  have hfin : (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), ⨆ i, v.val (u i))
      ≤ ∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), ⨆ i, v.val (w i) := by
    refine finprod_le_finprod (by fun_prop)
      (fun v => Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v.val _)) (by fun_prop) ?_
    intro v
    exact hnonarch v
  have hfin_u_nonneg : 0 ≤ (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      ⨆ i, v.val (u i)) := finprod_nonneg (fun v => Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v.val _))
  have hfin_w_nonneg : 0 ≤ (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      ⨆ i, v.val (w i)) := finprod_nonneg (fun v => Real.iSup_nonneg (fun i => AbsoluteValue.nonneg v.val _))
  calc (∏ v : NumberField.InfinitePlace K, (⨆ i, v (u i)) ^ v.mult)
        * (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), ⨆ i, v.val (u i))
      ≤ ((2 : ℝ) ^ Module.finrank ℚ K
          * ∏ v : NumberField.InfinitePlace K, (⨆ i, v (w i)) ^ v.mult)
        * (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), ⨆ i, v.val (w i)) :=
        mul_le_mul harch_prod hfin hfin_u_nonneg
          (mul_nonneg (by positivity) (Finset.prod_nonneg fun v _ => pow_nonneg (harch_nonneg_w v) _))
    _ = (2 : ℝ) ^ Module.finrank ℚ K
        * ((∏ v : NumberField.InfinitePlace K, (⨆ i, v (w i)) ^ v.mult)
          * (∏ᶠ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K), ⨆ i, v.val (w i))) := by
        ring

/-- Logarithmic form of `mulHeight_le_of_arch_two`: the archimedean factor 2
contributes exactly `finrank * log 2`. -/
lemma logHeight_le_of_arch_two {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (u : ι → K) (w : ι' → K) (hu : u ≠ 0) (hw : w ≠ 0)
    (hnonarch : ∀ v : Height.AdmissibleAbsValues.nonarchAbsVal (K := K),
      (⨆ i : ι, v.val (u i)) ≤ ⨆ j : ι', v.val (w j))
    (harch : ∀ v : NumberField.InfinitePlace K,
      (⨆ i : ι, v (u i)) ≤ 2 * ⨆ j : ι', v (w j)) :
    Height.logHeight u ≤ Height.logHeight w + (Module.finrank ℚ K : ℝ) * Real.log 2 := by
  rw [Height.logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight]
  have h := mulHeight_le_of_arch_two u w hu hw hnonarch harch
  have hupos : 0 < Height.mulHeight u := Height.mulHeight_pos u
  have hwpos : 0 < Height.mulHeight w := Height.mulHeight_pos w
  calc Real.log (Height.mulHeight u)
      ≤ Real.log ((2 : ℝ) ^ Module.finrank ℚ K * Height.mulHeight w) :=
        Real.log_le_log hupos h
    _ = Real.log (Height.mulHeight w) + (Module.finrank ℚ K : ℝ) * Real.log 2 := by
        rw [Real.log_mul (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)) (ne_of_gt hwpos),
          Real.log_pow]
        ring

#print axioms mulHeight_le_of_arch_two
#print axioms logHeight_le_of_arch_two

/-! ## Multi-coordinate versions (requested by the §8.2 lane) -/

/-- Nonarchimedean: a finite sum bounded termwise by a constant is bounded by it. -/
lemma nonarch_sum_le_of_le {ι : Type*} (s : Finset ι) {v : AbsoluteValue K ℝ}
    (hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y)) (f : ι → K) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ i ∈ s, v (f i) ≤ C) : v (∑ i ∈ s, f i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : v (f a + ∑ i ∈ s, f i) ≤ max (v (f a)) (v (∑ i ∈ s, f i)) := hna _ _
      have h2 : v (f a) ≤ C := hf a (Finset.mem_insert_self _ _)
      have h3 : v (∑ i ∈ s, f i) ≤ C := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      exact le_trans h1 (max_le h2 h3)

/-- Nonarchimedean version for a sum minus one term. -/
lemma nonarch_sum_sub_le_of_le {ι : Type*} (s : Finset ι) {v : AbsoluteValue K ℝ}
    (hna : ∀ x y : K, v (x + y) ≤ max (v x) (v y)) (f : ι → K) (b : K) {C : ℝ} (hC : 0 ≤ C)
    (hb : v b ≤ C) (hf : ∀ i ∈ s, v (f i) ≤ C) : v (∑ i ∈ s, f i - b) ≤ C := by
  refine le_trans (nonarch_sub_le_max (v := v) hna (∑ i ∈ s, f i) b) (max_le ?_ hb)
  exact nonarch_sum_le_of_le s hna f hC hf

/-- Archimedean: a finite sum has height at most `card * C`. -/
lemma arch_sum_le_card_mul {ι : Type*} (s : Finset ι) {v : AbsoluteValue K ℝ}
    (f : ι → K) {C : ℝ} (hC : 0 ≤ C) (hf : ∀ i ∈ s, v (f i) ≤ C) :
    v (∑ i ∈ s, f i) ≤ s.card * C := by
  have h1 := AbsoluteValue.sum_le v s f
  have h2 : (∑ i ∈ s, v (f i)) ≤ s.card * C := by
    calc (∑ i ∈ s, v (f i)) ≤ ∑ _i ∈ s, C := Finset.sum_le_sum hf
      _ = s.card * C := by rw [Finset.sum_const, nsmul_eq_mul]
  exact le_trans h1 h2

/-- Archimedean version for a sum minus one term: factor `card + 1`. -/
lemma arch_sum_sub_le_card_mul {ι : Type*} (s : Finset ι) {v : AbsoluteValue K ℝ}
    (f : ι → K) (b : K) {C : ℝ} (hC : 0 ≤ C) (hb : v b ≤ C)
    (hf : ∀ i ∈ s, v (f i) ≤ C) : v (∑ i ∈ s, f i - b) ≤ (s.card + 1) * C := by
  have h1 : v (∑ i ∈ s, f i - b) ≤ v (∑ i ∈ s, f i) + v b :=
    AbsoluteValue.sub_le_add v _ _
  have h2 : v (∑ i ∈ s, f i) ≤ s.card * C := arch_sum_le_card_mul s f hC hf
  calc v (∑ i ∈ s, f i - b) ≤ v (∑ i ∈ s, f i) + v b := h1
    _ ≤ s.card * C + C := add_le_add h2 hb
    _ = (s.card + 1) * C := by ring

#print axioms nonarch_sum_le_of_le
#print axioms nonarch_sum_sub_le_of_le
#print axioms arch_sum_le_card_mul
#print axioms arch_sum_sub_le_card_mul

end LeanFormal.IUT.XiFPaper.F8LocalActual
end