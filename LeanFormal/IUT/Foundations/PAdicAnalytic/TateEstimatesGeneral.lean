import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace LeanFormal.IUT.PAdicAnalytic

set_option linter.unusedSectionVars false

noncomputable section

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- General analytic remainder R(q) = sum_{n>=0} h_{n+2} q^{n+2}. -/
def generalTateRemainder (h : ℕ → K) (q : K) : K :=
  ∑' n : ℕ, h (n + 2) * q ^ (n + 2)

lemma summable_generalTateRemainder (h : ℕ → K) (hh : ∀ n, ‖h n‖ ≤ 1)
    {q : K} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => h (n + 2) * q ^ (n + 2) := by
  have hgeom : Summable fun n : ℕ => ‖q‖ ^ (n + 2) :=
    (summable_nat_add_iff 2).mpr
      (summable_geometric_of_lt_one (norm_nonneg q) hq)
  refine Summable.of_norm ?_
  refine hgeom.of_nonneg_of_le (fun n => norm_nonneg _) ?_
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg q) _) (hh (n + 2))

lemma general_norm_pow_sub_pow_le {x y : K} (m : ℕ) (hm : 1 ≤ m) :
    ‖x ^ m - y ^ m‖ ≤ ‖x - y‖ * max ‖x‖ ‖y‖ ^ (m - 1) := by
  let M : ℝ := max ‖x‖ ‖y‖
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg x) (le_max_left _ _)
  have hgeom : (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) * (x - y) =
      x ^ m - y ^ m := (Commute.all x y).geom_sum₂_mul m
  rw [← hgeom, norm_mul, mul_comm (‖x - y‖) (M ^ (m - 1))]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (x - y))
  have hsum : ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖ ≤ M ^ (m - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (C := M ^ (m - 1)) (pow_nonneg hMnonneg _) ?_
    intro i hi
    rw [norm_mul, norm_pow, norm_pow]
    have hi_m : i < m := Finset.mem_range.mp hi
    have hxi : ‖x‖ ^ i ≤ M ^ i :=
      pow_le_pow_left₀ (norm_nonneg x) (le_max_left _ _) i
    have hyi : ‖y‖ ^ (m - 1 - i) ≤ M ^ (m - 1 - i) :=
      pow_le_pow_left₀ (norm_nonneg y) (le_max_right _ _) _
    calc
      ‖x‖ ^ i * ‖y‖ ^ (m - 1 - i) ≤ M ^ i * M ^ (m - 1 - i) :=
        mul_le_mul hxi hyi (pow_nonneg (norm_nonneg y) _) (pow_nonneg hMnonneg _)
      _ = M ^ (i + (m - 1 - i)) := by rw [← pow_add]
      _ = M ^ (m - 1) := by
        congr 1
        omega
  exact hsum

theorem generalTateRemainder_norm_le_of_le_c (h : ℕ → K) (hh : ∀ n, ‖h n‖ ≤ 1)
    {c : ℝ} (hc1 : c < 1) {q : K} (hq : ‖q‖ ≤ c) :
    ‖generalTateRemainder h q‖ ≤ ‖q‖ ^ 2 := by
  have hq1 : ‖q‖ < 1 := hq.trans_lt hc1
  have hs := summable_generalTateRemainder h hh hq1
  let g : ℕ → K := fun n => h (n + 2) * q ^ (n + 2)
  have hpartial : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, g i) Filter.atTop
      (nhds (generalTateRemainder h q)) := by
    simpa [g, generalTateRemainder] using hs.hasSum.tendsto_sum_nat
  have hnormpartial : Filter.Tendsto (fun n : ℕ => ‖∑ i ∈ Finset.range n, g i‖)
      Filter.atTop (nhds ‖generalTateRemainder h q‖) :=
    (continuous_norm.tendsto _).comp hpartial
  have hbound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, g i‖ ≤ ‖q‖ ^ 2 := by
    intro n
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (C := ‖q‖ ^ 2) (pow_nonneg (norm_nonneg q) 2)
    intro i hi
    change ‖h (i + 2) * q ^ (i + 2)‖ ≤ ‖q‖ ^ 2
    rw [norm_mul, norm_pow]
    have hc : ‖h (i + 2)‖ ≤ 1 := hh _
    have hqle : ‖q‖ ≤ 1 := hq1.le
    have hpow : ‖q‖ ^ (i + 2) ≤ ‖q‖ ^ 2 :=
      pow_le_pow_of_le_one (norm_nonneg q) hqle (by omega)
    calc
      ‖h (i + 2)‖ * ‖q‖ ^ (i + 2) ≤ 1 * ‖q‖ ^ (i + 2) :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg q) _)
      _ = ‖q‖ ^ (i + 2) := one_mul _
      _ ≤ ‖q‖ ^ 2 := hpow
  exact le_of_tendsto_of_tendsto' hnormpartial tendsto_const_nhds hbound

/-- The c^2 form of the quadratic remainder bound. -/
theorem generalTateRemainder_norm_le_c_sq (h : ℕ → K) (hh : ∀ n, ‖h n‖ ≤ 1)
    {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c < 1) {q : K} (hq : ‖q‖ ≤ c) :
    ‖generalTateRemainder h q‖ ≤ c ^ 2 :=
  (generalTateRemainder_norm_le_of_le_c h hh hc1 hq).trans
    (pow_le_pow_left₀ (norm_nonneg q) hq 2)

theorem generalTateRemainder_lipschitz_c (h : ℕ → K) (hh : ∀ n, ‖h n‖ ≤ 1)
    {c : ℝ} (hc1 : c < 1) {x y : K}
    (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) :
    ‖generalTateRemainder h x - generalTateRemainder h y‖ ≤ c * ‖x - y‖ := by
  have hx1 : ‖x‖ < 1 := hx.trans_lt hc1
  have hy1 : ‖y‖ < 1 := hy.trans_lt hc1
  let gx : ℕ → K := fun n => h (n + 2) * x ^ (n + 2)
  let gy : ℕ → K := fun n => h (n + 2) * y ^ (n + 2)
  have hsx : Summable gx := by simpa [gx] using summable_generalTateRemainder h hh hx1
  have hsy : Summable gy := by simpa [gy] using summable_generalTateRemainder h hh hy1
  have hd : generalTateRemainder h x - generalTateRemainder h y = ∑' n, (gx n - gy n) := by
    rw [generalTateRemainder, generalTateRemainder, ← hsx.tsum_sub hsy]
  rw [hd]
  let M : ℝ := max ‖x‖ ‖y‖
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg x) (le_max_left _ _)
  have hMle : M ≤ c := max_le hx hy
  have hMle1 : M ≤ 1 := hMle.trans hc1.le
  have hterm : ∀ n : ℕ, ‖gx n - gy n‖ ≤ M * ‖x - y‖ := by
    intro n
    change ‖h (n + 2) * x ^ (n + 2) - h (n + 2) * y ^ (n + 2)‖ ≤ M * ‖x - y‖
    rw [← mul_sub, norm_mul]
    have hc : ‖h (n + 2)‖ ≤ 1 := hh _
    have hpow := general_norm_pow_sub_pow_le (x := x) (y := y) (n + 2) (by omega)
    have hMpow : M ^ (n + 1) ≤ M := by
      calc
        M ^ (n + 1) ≤ M ^ 1 := pow_le_pow_of_le_one hMnonneg hMle1 (by omega)
        _ = M := pow_one M
    have hdiff : ‖x - y‖ * M ^ (n + 1) ≤ ‖x - y‖ * M :=
      mul_le_mul_of_nonneg_left hMpow (norm_nonneg _)
    calc
      ‖h (n + 2)‖ * ‖x ^ (n + 2) - y ^ (n + 2)‖
          ≤ 1 * (‖x - y‖ * M ^ (n + 1)) := by
            exact mul_le_mul hc hpow (norm_nonneg _) (by norm_num)
      _ = ‖x - y‖ * M ^ (n + 1) := one_mul _
      _ ≤ ‖x - y‖ * M := hdiff
      _ = M * ‖x - y‖ := mul_comm _ _
  have hsd : Summable fun n : ℕ => gx n - gy n := hsx.sub hsy
  have hpartial : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (gx i - gy i))
      Filter.atTop (nhds (∑' n, (gx n - gy n))) := hsd.hasSum.tendsto_sum_nat
  have hnormpartial : Filter.Tendsto
      (fun n : ℕ => ‖∑ i ∈ Finset.range n, (gx i - gy i)‖)
      Filter.atTop (nhds ‖∑' n, (gx n - gy n)‖) :=
    (continuous_norm.tendsto _).comp hpartial
  have hbound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, (gx i - gy i)‖ ≤ M * ‖x - y‖ := by
    intro n
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (C := M * ‖x - y‖) (mul_nonneg hMnonneg (norm_nonneg _))
    intro i hi
    exact hterm i
  have hmain : ‖∑' n, (gx n - gy n)‖ ≤ M * ‖x - y‖ :=
    le_of_tendsto_of_tendsto' hnormpartial tendsto_const_nhds hbound
  exact hmain.trans (mul_le_mul_of_nonneg_right hMle (norm_nonneg _))

theorem generalTateRemainder_norm_le (h : ℕ → K) (hh : ∀ n, ‖h n‖ ≤ 1)
    (p : ℕ) {q : K} (hq : ‖q‖ ≤ ‖(p : K)‖) (hp : ‖(p : K)‖ < 1) :
    ‖generalTateRemainder h q‖ ≤ ‖q‖ ^ 2 :=
  generalTateRemainder_norm_le_of_le_c h hh hp hq

theorem generalTateRemainder_lipschitz (h : ℕ → K) (hh : ∀ n, ‖h n‖ ≤ 1)
    (p : ℕ) (hp : ‖(p : K)‖ < 1) {x y : K}
    (hx : ‖x‖ ≤ ‖(p : K)‖) (hy : ‖y‖ ≤ ‖(p : K)‖) :
    ‖generalTateRemainder h x - generalTateRemainder h y‖ ≤
      ‖(p : K)‖ * ‖x - y‖ :=
  generalTateRemainder_lipschitz_c h hh hp hx hy
end

end LeanFormal.IUT.PAdicAnalytic
