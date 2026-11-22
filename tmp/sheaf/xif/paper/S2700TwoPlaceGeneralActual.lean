import tmp.sheaf.xif.paper.S2699LogQ2161Actual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume

namespace LeanFormal.IUT.XiFPaper.S2700TwoPlaceGeneralActual

local instance s2700GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2700_log_le_abs_log
    {p : NumberField.FinitePlace GaussianField}
    (c : ℝ) (hc : 0 < c) (hp : c ≤ residueNormBase p)
    (parameter : FinitePlaceQCandidate p) :
    Real.log c ≤ |Real.log ‖parameter.q‖| := by
  have hlog : Real.log c ≤ Real.log (residueNormBase p) :=
    Real.log_le_log hc hp
  have hpos : 0 < Real.log (residueNormBase p) :=
    log_residueNormBase_pos p
  have horder : (1 : ℝ) ≤ (parameter.order : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt parameter.order_pos
  have habs : |Real.log ‖parameter.q‖| = localLogMagnitude parameter := by
    simpa only [localSignedLog] using abs_localSignedLog parameter
  rw [habs, localLogMagnitude_eq_order_mul_log]
  calc
    Real.log c ≤ Real.log (residueNormBase p) := hlog
    _ = (1 : ℝ) * Real.log (residueNormBase p) := (one_mul _).symm
    _ ≤ (parameter.order : ℝ) * Real.log (residueNormBase p) :=
      mul_le_mul_of_nonneg_right horder (le_of_lt hpos)

theorem S2700_five_log_le_abs_log
    (parameter : FinitePlaceQCandidate concreteGaussianFivePlace) :
    Real.log (5 : ℝ) ≤ |Real.log ‖parameter.q‖| := by
  have h5 : residueNormBase concreteGaussianFivePlace = 5 := by
    simpa [S1487FivePlace] using S1487_residueNormBase_five
  refine S2700_log_le_abs_log (p := concreteGaussianFivePlace) 5 (by norm_num) ?_ parameter
  rw [h5]

theorem S2700_2161_log_le_abs_log
    (parameter : FinitePlaceQCandidate S2696GaussianPlace) :
    Real.log (2161 : ℝ) ≤ |Real.log ‖parameter.q‖| :=
  S2700_log_le_abs_log (p := S2696GaussianPlace) 2161 (by norm_num)
    S2698_residueNormBase_ge parameter

noncomputable def S2700TwoPlaceLogVolume
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161 : FinitePlaceQCandidate S2696GaussianPlace) : ℝ :=
  |Real.log ‖q5.q‖| + |Real.log ‖q2161.q‖|

theorem S2700_twoPlace_ge
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161 : FinitePlaceQCandidate S2696GaussianPlace) :
    Real.log (5 : ℝ) + Real.log (2161 : ℝ) ≤
      S2700TwoPlaceLogVolume q5 q2161 := by
  unfold S2700TwoPlaceLogVolume
  linarith [S2700_five_log_le_abs_log q5, S2700_2161_log_le_abs_log q2161]

theorem S2700_twoPlace_gt_two_log5
    (q5 : FinitePlaceQCandidate concreteGaussianFivePlace)
    (q2161 : FinitePlaceQCandidate S2696GaussianPlace) :
    2 * Real.log (5 : ℝ) < S2700TwoPlaceLogVolume q5 q2161 := by
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith [S2700_twoPlace_ge q5 q2161, hlt]

#check S2700_log_le_abs_log
#check S2700_five_log_le_abs_log
#check S2700_2161_log_le_abs_log
#check S2700_twoPlace_ge
#check S2700_twoPlace_gt_two_log5
#print axioms S2700_twoPlace_ge
#print axioms S2700_twoPlace_gt_two_log5

end LeanFormal.IUT.XiFPaper.S2700TwoPlaceGeneralActual
end
