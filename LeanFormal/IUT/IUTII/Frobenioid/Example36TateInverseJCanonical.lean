import LeanFormal.IUT.IUTII.Frobenioid.Example36TateUniformization
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateContraction
import LeanFormal.IUT.Foundations.PAdicAnalytic.TateQSeriesEval

open LeanFormal.IUT
open LeanFormal.IUT.PAdicAnalytic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ

local instance fivePrimeFactCanonical : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

local instance concreteSplitCurveLocalIsEllipticCanonical :
    concreteSplitCurveLocal.IsElliptic := concreteSplitCurveLocal_isElliptic

/-- The concrete model inverse-j parameter supplied by the contraction fixed point
also satisfies the canonical q-series inverse-j relation for the split curve.
This is model-only: t = -10805, ball radius 1/25, contraction 1/5. -/
theorem exists_canonicalQSeriesJ_eq_split_j :
    ∃ q : concreteLocalField,
      padicEval tateHFormal q = PAdicAnalytic.tateT ∧
      canonicalQSeriesJ q = concreteSplitCurveLocal.j ∧
      q ≠ 0 ∧ ‖q‖ < 1 ∧ ‖q‖ ≤ 1 / 5 ∧
      dist q (PAdicAnalytic.tateT) ≤ 1 / 25 := by
  obtain ⟨q, hH, hqle, hqdist⟩ := PAdicAnalytic.exists_tateH_eq_t
  have hq1 : ‖q‖ < 1 := hqle.trans_lt (by norm_num)
  have hbridge : padicEval tateHFormal q = padicPowerSeriesEval tateHFormal q := rfl
  have hHdelta :
      (TateCurve.weierstrassCurve ℚ_[5] q).Δ /
          (TateCurve.weierstrassCurve ℚ_[5] q).c₄ ^ 3 =
        (PAdicAnalytic.tateT : ℚ_[5]) := by
    rw [← padicPowerSeriesEval_tateHFormal hq1, ← hbridge]
    exact hH
  have ht_ne : (PAdicAnalytic.tateT : ℚ_[5]) ≠ 0 := by
    rw [PAdicAnalytic.tateT]
    norm_num
  have hc4ne : (TateCurve.weierstrassCurve ℚ_[5] q).c₄ ^ 3 ≠ 0 := by
    intro hzero
    have hz : (0 : ℚ_[5]) = PAdicAnalytic.tateT := by
      simpa [hzero] using hHdelta
    exact ht_ne hz.symm
  have hdelta_eq :
      (TateCurve.weierstrassCurve ℚ_[5] q).Δ =
        (PAdicAnalytic.tateT : ℚ_[5]) *
          (TateCurve.weierstrassCurve ℚ_[5] q).c₄ ^ 3 :=
    (div_eq_iff hc4ne).mp hHdelta
  have hdelta_ne : (TateCurve.weierstrassCurve ℚ_[5] q).Δ ≠ 0 := by
    rw [hdelta_eq]
    exact mul_ne_zero ht_ne hc4ne
  have hc4 : (TateCurve.weierstrassCurve ℚ_[5] q).c₄ ≠ 0 := by
    intro hzero
    exact hc4ne (by rw [hzero]; ring)
  have hcanon : canonicalQSeriesJ q = (PAdicAnalytic.tateT : ℚ_[5])⁻¹ := by
    rw [canonicalQSeriesJ, hdelta_eq]
    field_simp [hc4, ht_ne]
  have hqne : q ≠ 0 := by
    intro hq0
    have hdist0 : dist q (PAdicAnalytic.tateT) = ‖PAdicAnalytic.tateT‖ := by
      rw [hq0]
      exact dist_zero_left _
    rw [hdist0, PAdicAnalytic.norm_tateT] at hqdist
    norm_num at hqdist
  refine ⟨q, hH, ?_, hqne, hq1, hqle, hqdist⟩
  calc
    canonicalQSeriesJ q = (PAdicAnalytic.tateT : ℚ_[5])⁻¹ := hcanon
    _ = (-10805 : ℚ_[5])⁻¹ := by rw [PAdicAnalytic.tateT]
    _ = -1 / 10805 := by norm_num
    _ = concreteSplitCurveLocal.j := by rw [concreteSplitCurveLocal_j_eq]


/-- Strengthened model-only inverse-j statement: also norm q = 1/5 and
q congruent to -5 mod 25 (in the sense dist q (-5) <= 1/25). -/
theorem exists_canonicalQSeriesJ_eq_split_j_full :
    ∃ q : concreteLocalField,
      padicEval tateHFormal q = PAdicAnalytic.tateT ∧
      canonicalQSeriesJ q = concreteSplitCurveLocal.j ∧
      q ≠ 0 ∧ ‖q‖ < 1 ∧ ‖q‖ = 1 / 5 ∧
      dist q (-5 : ℚ_[5]) ≤ 1 / 25 := by
  obtain ⟨q, hH, hcanon, hqne, hq1, hqle, hqdist⟩ :=
    exists_canonicalQSeriesJ_eq_split_j
  have ht5 : dist (PAdicAnalytic.tateT) (-5 : ℚ_[5]) ≤ 1 / 25 := by
    rw [dist_eq_norm]
    have hdiff : PAdicAnalytic.tateT - (-5 : ℚ_[5]) = (-10800 : ℚ_[5]) := by
      rw [PAdicAnalytic.tateT]
      norm_num
    rw [hdiff]
    have hfac : (-10800 : ℚ_[5]) = -((25 : ℚ_[5]) * (432 : ℚ_[5])) := by norm_num
    rw [hfac, norm_neg, norm_mul]
    have h25 : ‖(25 : ℚ_[5])‖ = (1 / 25 : ℝ) := by
      have h := Padic.norm_p_pow (p := 5) 2
      norm_num at h
      convert h using 1
    have h432 : ‖(432 : ℚ_[5])‖ = 1 := by
      change ‖((432 : ℕ) : ℚ_[5])‖ = 1
      rw [Padic.norm_natCast_eq_one_iff]
      decide
    rw [h25, h432]
    norm_num
  have hq_ge : 1 / 5 ≤ ‖q‖ := by
    have ht_le : (1 / 5 : ℝ) ≤ max (dist (PAdicAnalytic.tateT) q) ‖q‖ := by
      have h := IsUltrametricDist.dist_triangle_max (PAdicAnalytic.tateT) q (0 : ℚ_[5])
      rw [dist_zero_right, PAdicAnalytic.norm_tateT] at h
      simpa [dist_comm] using h
    have hmaxle : max (dist (PAdicAnalytic.tateT) q) ‖q‖ ≤ max (1 / 25 : ℝ) ‖q‖ :=
      max_le_max (by simpa [dist_comm] using hqdist) le_rfl
    have hge : (1 / 5 : ℝ) ≤ max (1 / 25 : ℝ) ‖q‖ := ht_le.trans hmaxle
    by_contra hlt
    push_neg at hlt
    have hmax_lt : max (1 / 25 : ℝ) ‖q‖ < 1 / 5 := max_lt (by norm_num) hlt
    exact (not_lt_of_ge hge) hmax_lt
  have hnorm_eq : ‖q‖ = 1 / 5 := le_antisymm hqle hq_ge
  have hdist_neg5 : dist q (-5 : ℚ_[5]) ≤ 1 / 25 := by
    have h := IsUltrametricDist.dist_triangle_max q (PAdicAnalytic.tateT) (-5 : ℚ_[5])
    exact h.trans (max_le hqdist ht5)
  exact ⟨q, hH, hcanon, hqne, hq1, hnorm_eq, hdist_neg5⟩


end LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ
