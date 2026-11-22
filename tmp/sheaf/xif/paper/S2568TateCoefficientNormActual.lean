import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Order.Field
open Filter Topology

noncomputable section
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S2568TateCoefficientNormActual

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

theorem S2568_norm_one_sub_qpow {q : K} (hq : ‖q‖ < 1)
    (n : Nat) (hn : 0 < n) : ‖(1 : K) - q ^ n‖ = 1 := by
  have hpow : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn.ne'
  have hmax : (1 : ℝ) ≤ max ‖(1 : K) - q ^ n‖ ‖q ^ n‖ := by
    have h := IsUltrametricDist.norm_add_le_max ((1 : K) - q ^ n) (q ^ n)
    rw [sub_add_cancel, norm_one] at h
    exact h
  apply le_antisymm
  · have h := IsUltrametricDist.norm_add_le_max (1 : K) (-(q ^ n))
    have h' : ‖(1 : K) - q ^ n‖ ≤ max 1 ‖q ^ n‖ := by
      simpa [sub_eq_add_neg, norm_neg] using h
    refine h'.trans ?_
    rw [max_eq_left hpow.le]
  · by_contra hlt
    have h1 : ‖(1 : K) - q ^ n‖ < 1 := lt_of_not_ge hlt
    have hmaxlt : max ‖(1 : K) - q ^ n‖ ‖q ^ n‖ < 1 := max_lt h1 hpow
    linarith

theorem S2568_norm_lambert_term_le (weight n : Nat) {q : K} (hq : ‖q‖ < 1)
    (hn : 0 < n) :
    ‖(n : K) ^ weight * q ^ n / (1 - q ^ n)‖ ≤ ‖q‖ := by
  rw [norm_div, norm_mul, norm_pow, S2568_norm_one_sub_qpow hq n hn, div_one]
  have hnat : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  have hqpow : ‖q ^ n‖ ≤ ‖q‖ := by
    rw [norm_pow]
    exact pow_le_of_le_one (norm_nonneg q) hq.le hn.ne'
  have hnatpow : ‖(n : K)‖ ^ weight ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hnat
  calc ‖(n : K)‖ ^ weight * ‖q ^ n‖
      ≤ 1 * ‖q‖ := mul_le_mul hnatpow hqpow (norm_nonneg _) zero_le_one
    _ = ‖q‖ := one_mul _

theorem S2568_norm_tsum_le_of_bound {ι : Type*} (f : ι → K) (a : K)
    (c : ℝ) (hc : 0 ≤ c) (hf : HasSum f a) (h : ∀ i, ‖f i‖ ≤ c) :
    ‖a‖ ≤ c := by
  classical
  open Filter in
  let g : Finset ι → K := fun s => ∑ i ∈ s, f i
  have hg : ∀ s, ‖g s‖ ≤ c := by
    intro s
    induction s using Finset.induction with
    | empty => simpa [g] using hc
    | insert a s ha ih =>
        change ‖∑ i ∈ insert a s, f i‖ ≤ c
        rw [Finset.sum_insert ha]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h a) ih)
  have hlim : Tendsto g atTop (nhds a) := hf
  have hclosed : IsClosed {x : K | ‖x‖ ≤ c} :=
    isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hg)

theorem S2568_lambertSeries_norm_le (weight : Nat) (hweight : 0 < weight)
    {q : K} (hq : ‖q‖ < 1) :
    ‖TateCurve.lambertSeries K weight q‖ ≤ ‖q‖ := by
  have hsum := TateCurve.lambertSeries_summable K weight hq
  refine S2568_norm_tsum_le_of_bound
    (fun n : Nat => (n : K) ^ weight * q ^ n / (1 - q ^ n))
    (TateCurve.lambertSeries K weight q) ‖q‖ (norm_nonneg q) hsum.hasSum ?_
  intro n
  by_cases hn : n = 0
  · subst n; simp [hweight]
  · exact S2568_norm_lambert_term_le weight n hq (Nat.pos_of_ne_zero hn)

theorem S2568_norm_a4_le {q : K} (hq : ‖q‖ < 1) :
    ‖TateCurve.a4 K q‖ ≤ ‖q‖ := by
  unfold TateCurve.a4
  rw [norm_mul, norm_neg]
  calc ‖(5 : K)‖ * ‖TateCurve.lambertSeries K 3 q‖
      ≤ 1 * ‖q‖ := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one K 5
        · exact S2568_lambertSeries_norm_le 3 (by norm_num) hq
    _ = ‖q‖ := one_mul _

theorem S2568_norm_a6_le [CharZero K] {q : K} (hq : ‖q‖ < 1)
    (h12 : ‖(12 : K)‖ = 1) :
    ‖TateCurve.a6 K q‖ ≤ ‖q‖ := by
  unfold TateCurve.a6
  rw [norm_div, norm_neg]
  have h3 := S2568_lambertSeries_norm_le 3 (by norm_num) hq
  have h5 := S2568_lambertSeries_norm_le 5 (by norm_num) hq
  have hnum : ‖(5 : K) * TateCurve.lambertSeries K 3 q +
      7 * TateCurve.lambertSeries K 5 q‖ ≤ ‖q‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖(5 : K)‖ * ‖TateCurve.lambertSeries K 3 q‖
          ≤ 1 * ‖q‖ := by
            gcongr
            exact IsUltrametricDist.norm_natCast_le_one K 5
        _ = ‖q‖ := one_mul _
    · rw [norm_mul]
      calc ‖(7 : K)‖ * ‖TateCurve.lambertSeries K 5 q‖
          ≤ 1 * ‖q‖ := by
            gcongr
            exact IsUltrametricDist.norm_natCast_le_one K 7
        _ = ‖q‖ := one_mul _
  calc ‖(5 : K) * TateCurve.lambertSeries K 3 q +
        7 * TateCurve.lambertSeries K 5 q‖ / ‖(12 : K)‖
      ≤ ‖q‖ / 1 := by
        gcongr
        rw [h12]
    _ = ‖q‖ := div_one _

#check S2568_norm_a4_le
#check S2568_norm_a6_le
#print axioms S2568_norm_a4_le
end LeanFormal.IUT.XiFPaper.S2568TateCoefficientNormActual
end