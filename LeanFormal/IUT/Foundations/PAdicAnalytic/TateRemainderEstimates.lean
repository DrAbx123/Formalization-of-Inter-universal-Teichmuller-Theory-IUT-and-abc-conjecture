import LeanFormal.IUT.Foundations.PAdicAnalytic.PadicEvalBridge
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesCoefficients
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open LeanFormal.IUT.PAdicAnalytic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic

noncomputable section

local instance fivePrimeFactTR : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The analytic remainder R(q) = sum_{n>=2} h_n q^n of the formal H. -/
noncomputable def tateHRemainder (q : ℚ_[5]) : ℚ_[5] :=
  ∑' n : ℕ, (tateHFormal.coeff (n + 2) : ℚ_[5]) * q ^ (n + 2)

lemma summable_tateHRemainder {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => (tateHFormal.coeff (n + 2) : ℚ_[5]) * q ^ (n + 2) := by
  have hs : Summable fun n : ℕ => padicCoeffTerm tateHFormal q (n + 2) :=
    (summable_nat_add_iff 2).mpr (summable_padicCoeffTerm tateHFormal hq)
  simpa [padicCoeffTerm, Nat.add_comm] using hs

lemma tateHRemainder_norm_le {q : ℚ_[5]} (hq : ‖q‖ ≤ 1 / 5) :
    ‖tateHRemainder q‖ ≤ ‖q‖ ^ 2 := by
  have hq1 : ‖q‖ < 1 := hq.trans_lt (by norm_num)
  have hs := summable_tateHRemainder hq1
  let g : ℕ → ℚ_[5] := fun n => (tateHFormal.coeff (n + 2) : ℚ_[5]) * q ^ (n + 2)
  have hpartial : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, g i) Filter.atTop
      (nhds (tateHRemainder q)) := by
    simpa [g, tateHRemainder] using hs.hasSum.tendsto_sum_nat
  have hnormpartial : Filter.Tendsto (fun n : ℕ => ‖∑ i ∈ Finset.range n, g i‖) Filter.atTop
      (nhds ‖tateHRemainder q‖) :=
    (continuous_norm.tendsto _).comp hpartial
  have hbound : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, g i‖ ≤ ‖q‖ ^ 2 := by
    intro n
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (C := ‖q‖ ^ 2) (pow_nonneg (norm_nonneg q) 2)
    intro i hi
    change ‖(tateHFormal.coeff (i + 2) : ℚ_[5]) * q ^ (i + 2)‖ ≤ ‖q‖ ^ 2
    rw [norm_mul, norm_pow]
    have hc : ‖((tateHFormal.coeff (i + 2) : ℚ_[5]))‖ ≤ 1 := by
      simpa using PadicInt.norm_le_one (tateHFormal.coeff (i + 2))
    have hqle : ‖q‖ ≤ 1 := hq.trans (by norm_num)
    have hpow : ‖q‖ ^ (i + 2) ≤ ‖q‖ ^ 2 :=
      pow_le_pow_of_le_one (norm_nonneg q) hqle (by omega)
    calc
      ‖(tateHFormal.coeff (i + 2) : ℚ_[5])‖ * ‖q‖ ^ (i + 2) ≤
          1 * ‖q‖ ^ (i + 2) :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg q) _)
      _ = ‖q‖ ^ (i + 2) := one_mul _
      _ ≤ ‖q‖ ^ 2 := hpow
  exact le_of_tendsto_of_tendsto' hnormpartial tendsto_const_nhds hbound


lemma norm_pow_sub_pow_le {x y : ℚ_[5]} (m : ℕ) (hm : 1 ≤ m) :
    ‖x ^ m - y ^ m‖ ≤ ‖x - y‖ * max ‖x‖ ‖y‖ ^ (m - 1) := by
  let M : ℝ := max ‖x‖ ‖y‖
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg x) (le_max_left _ _)
  have hgeom : (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) * (x - y) =
      x ^ m - y ^ m := (Commute.all x y).geom_sum₂_mul m
  rw [← hgeom, norm_mul, mul_comm (‖x - y‖) (M ^ (m - 1))]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (x - y))
  have hsum : ‖∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)‖ ≤ M ^ (m - 1) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (M := ℚ_[5]) (s := Finset.range m)
      (f := fun i => x ^ i * y ^ (m - 1 - i))
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



theorem tateHRemainder_lipschitz {x y : ℚ_[5]}
    (hx : ‖x‖ ≤ 1 / 5) (hy : ‖y‖ ≤ 1 / 5) :
    ‖tateHRemainder x - tateHRemainder y‖ ≤ max ‖x‖ ‖y‖ * ‖x - y‖ := by
  have hx1 : ‖x‖ < 1 := hx.trans_lt (by norm_num)
  have hy1 : ‖y‖ < 1 := hy.trans_lt (by norm_num)
  let gx : ℕ → ℚ_[5] := fun n =>
    (tateHFormal.coeff (n + 2) : ℚ_[5]) * x ^ (n + 2)
  let gy : ℕ → ℚ_[5] := fun n =>
    (tateHFormal.coeff (n + 2) : ℚ_[5]) * y ^ (n + 2)
  have hsx : Summable gx := by simpa [gx] using summable_tateHRemainder hx1
  have hsy : Summable gy := by simpa [gy] using summable_tateHRemainder hy1
  have hd : tateHRemainder x - tateHRemainder y = ∑' n, (gx n - gy n) := by
    rw [tateHRemainder, tateHRemainder, ← hsx.tsum_sub hsy]
  rw [hd]
  let M : ℝ := max ‖x‖ ‖y‖
  have hMnonneg : 0 ≤ M := le_trans (norm_nonneg x) (le_max_left _ _)
  have hMle : M ≤ 1 / 5 := max_le hx hy
  have hMle1 : M ≤ 1 := hMle.trans (by norm_num)
  have hterm : ∀ n : ℕ, ‖gx n - gy n‖ ≤ M * ‖x - y‖ := by
    intro n
    change ‖(tateHFormal.coeff (n + 2) : ℚ_[5]) * x ^ (n + 2) -
        (tateHFormal.coeff (n + 2) : ℚ_[5]) * y ^ (n + 2)‖ ≤ M * ‖x - y‖
    rw [← mul_sub, norm_mul]
    have hc : ‖((tateHFormal.coeff (n + 2) : ℚ_[5]))‖ ≤ 1 := by
      simpa using PadicInt.norm_le_one (tateHFormal.coeff (n + 2))
    have hpow := norm_pow_sub_pow_le (x := x) (y := y) (n + 2) (by omega)
    have hMpow : M ^ (n + 1) ≤ M := by
      calc
        M ^ (n + 1) ≤ M ^ 1 := pow_le_pow_of_le_one hMnonneg hMle1 (by omega)
        _ = M := pow_one M
    have hdiff : ‖x - y‖ * M ^ (n + 1) ≤ ‖x - y‖ * M :=
      mul_le_mul_of_nonneg_left hMpow (norm_nonneg _)
    calc
      ‖((tateHFormal.coeff (n + 2) : ℚ_[5]))‖ *
          ‖x ^ (n + 2) - y ^ (n + 2)‖
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
      (M := ℚ_[5]) (s := Finset.range n)
      (f := fun i => gx i - gy i) (C := M * ‖x - y‖)
      (mul_nonneg hMnonneg (norm_nonneg _))
    intro i hi
    exact hterm i
  exact le_of_tendsto_of_tendsto' hnormpartial tendsto_const_nhds hbound

theorem tateHRemainder_lipschitz_one_fifth {x y : ℚ_[5]}
    (hx : ‖x‖ ≤ 1 / 5) (hy : ‖y‖ ≤ 1 / 5) :
    ‖tateHRemainder x - tateHRemainder y‖ ≤ (1 / 5) * ‖x - y‖ := by
  have h := tateHRemainder_lipschitz hx hy
  have hM : max ‖x‖ ‖y‖ ≤ 1 / 5 := max_le hx hy
  exact h.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))


end
end LeanFormal.IUT.PAdicAnalytic
