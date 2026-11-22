import LeanFormal.IUT.Foundations.PAdicAnalytic.TateRemainderEstimates
import Mathlib.Topology.MetricSpace.Contracting

open LeanFormal.IUT.PAdicAnalytic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.PAdicAnalytic

noncomputable section

local instance fivePrimeFactTC : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Model-only constant t = j^{-1} = -10805 for the concrete Q_5 split curve. -/
noncomputable def tateT : ℚ_[5] := -10805

lemma norm_tateT : ‖tateT‖ = (1 / 5 : ℝ) := by
  have h5 : ‖(5 : ℚ_[5])‖ = (1 / 5 : ℝ) := by
    simpa using (Padic.norm_p (p := 5))
  have h2161 : ‖(2161 : ℚ_[5])‖ = 1 := by
    change ‖((2161 : ℕ) : ℚ_[5])‖ = 1
    rw [Padic.norm_natCast_eq_one_iff]
    decide
  have hcast : (10805 : ℚ_[5]) = (5 : ℚ_[5]) * (2161 : ℚ_[5]) := by norm_num
  calc
    ‖tateT‖ = ‖(10805 : ℚ_[5])‖ := by rw [tateT, norm_neg]
    _ = ‖(5 : ℚ_[5]) * (2161 : ℚ_[5])‖ := by rw [hcast]
    _ = ‖(5 : ℚ_[5])‖ * ‖(2161 : ℚ_[5])‖ := norm_mul _ _
    _ = (1 / 5 : ℝ) * 1 := by rw [h5, h2161]
    _ = 1 / 5 := by norm_num

abbrev tateBall : Set ℚ_[5] := Metric.closedBall tateT (1 / 25)

lemma norm_le_of_mem_tateBall {q : ℚ_[5]} (hq : q ∈ tateBall) :
    ‖q‖ ≤ 1 / 5 := by
  have hdist : ‖q - tateT‖ ≤ 1 / 25 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hq
  calc
    ‖q‖ = ‖(q - tateT) + tateT‖ := by ring_nf
    _ ≤ max ‖q - tateT‖ ‖tateT‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max (1 / 25 : ℝ) (1 / 5 : ℝ) :=
      max_le_max hdist (le_of_eq norm_tateT)
    _ = 1 / 5 := by norm_num

/-- The map T(q) = t - R(q) on the closed ball |q-t| <= 1/25. -/
noncomputable def tateMap (z : tateBall) : tateBall :=
  ⟨tateT - tateHRemainder z.1, by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hnorm : ‖z.1‖ ≤ 1 / 5 := norm_le_of_mem_tateBall z.2
    have hR : ‖tateHRemainder z.1‖ ≤ ‖z.1‖ ^ 2 := tateHRemainder_norm_le hnorm
    calc
      ‖(tateT - tateHRemainder z.1) - tateT‖ = ‖-tateHRemainder z.1‖ := by ring_nf
      _ = ‖tateHRemainder z.1‖ := norm_neg _
      _ ≤ ‖z.1‖ ^ 2 := hR
      _ ≤ (1 / 5 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 1 / 25 := by norm_num⟩

lemma tateMap_lipschitz : LipschitzWith (1 / 5 : NNReal) tateMap := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist (tateT - tateHRemainder z.1) (tateT - tateHRemainder w.1) ≤
    (1 / 5 : NNReal) * dist z.1 w.1
  rw [dist_eq_norm]
  have hx : ‖z.1‖ ≤ 1 / 5 := norm_le_of_mem_tateBall z.2
  have hy : ‖w.1‖ ≤ 1 / 5 := norm_le_of_mem_tateBall w.2
  have h := tateHRemainder_lipschitz_one_fifth hx hy
  rw [show (tateT - tateHRemainder z.1) - (tateT - tateHRemainder w.1) =
      -(tateHRemainder z.1 - tateHRemainder w.1) by ring, norm_neg]
  simpa [NNReal.coe_one, NNReal.coe_div, dist_eq_norm] using h

lemma tateMap_contracting : ContractingWith (1 / 5 : NNReal) tateMap :=
  ⟨by norm_num, tateMap_lipschitz⟩

theorem exists_tateHRemainder_fixed :
    ∃ q : ℚ_[5], q ∈ tateBall ∧ tateT - tateHRemainder q = q := by
  haveI : IsClosed (tateBall) := Metric.isClosed_closedBall
  haveI : CompleteSpace (tateBall) := inferInstance
  obtain ⟨z, hz⟩ := tateMap_contracting.exists_fixedPoint
    (x := ⟨tateT, by simp [Metric.mem_closedBall]⟩) (by simp)
  refine ⟨z.1, z.2, ?_⟩
  have hv := congrArg Subtype.val hz.1
  simpa [tateMap] using hv


lemma padicEval_tateHFormal_eq_add_remainder {q : ℚ_[5]} (hq : ‖q‖ < 1) :
    padicEval tateHFormal q = q + tateHRemainder q := by
  rw [padicEval]
  let f : ℕ → ℚ_[5] := fun n => (tateHFormal.coeff n : ℚ_[5]) * q ^ n
  have hs : Summable f := summable_padicCoeffTerm tateHFormal hq
  have hf0 : f 0 = 0 := by simp [f, coeff_tateHFormal_zero]
  change (∑' n : ℕ, f n) = q + tateHRemainder q
  rw [hs.tsum_eq_zero_add, hf0, zero_add]
  have hs1 : Summable fun n : ℕ => f (n + 1) := by
    simpa using (summable_nat_add_iff 1).mpr hs
  have hf1 : f 1 = q := by
    simp [f, coeff_tateHFormal_zero, coeff_tateHFormal_one]
  rw [hs1.tsum_eq_zero_add, hf1]
  congr 1

theorem exists_tateH_eq_t :
    ∃ q : ℚ_[5], padicEval tateHFormal q = tateT ∧
      ‖q‖ ≤ 1 / 5 ∧ dist q tateT ≤ 1 / 25 := by
  obtain ⟨q, hqball, hqfix⟩ := exists_tateHRemainder_fixed
  have hqle : ‖q‖ ≤ 1 / 5 := norm_le_of_mem_tateBall hqball
  have hq1 : ‖q‖ < 1 := hqle.trans_lt (by norm_num)
  refine ⟨q, ?_, hqle, hqball⟩
  rw [padicEval_tateHFormal_eq_add_remainder hq1]
  have hsum : q + tateHRemainder q = tateT := by
    nth_rewrite 1 [← hqfix]
    ring
  exact hsum


end
end LeanFormal.IUT.PAdicAnalytic
