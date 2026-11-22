import tmp.sheaf.xif.paper.S2698ResidueNorm2161Actual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696GaussianPlace2161Actual
open LeanFormal.IUT.XiFPaper.S2698ResidueNorm2161Actual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume

namespace LeanFormal.IUT.XiFPaper.S2699LogQ2161Actual

local instance s2699GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2699_log2161_le_log_residueNormBase :
    Real.log (2161 : ℝ) ≤ Real.log (residueNormBase S2696GaussianPlace) :=
  Real.log_le_log (by norm_num) S2698_residueNormBase_ge

theorem S2699_log2161_le_localLogMagnitude
    (parameter : FinitePlaceQCandidate S2696GaussianPlace) :
    Real.log (2161 : ℝ) ≤ localLogMagnitude parameter := by
  rw [localLogMagnitude_eq_order_mul_log]
  have horder : (1 : ℝ) ≤ (parameter.order : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt parameter.order_pos
  have hlogpos : 0 ≤ Real.log (residueNormBase S2696GaussianPlace) :=
    le_of_lt (log_residueNormBase_pos S2696GaussianPlace)
  calc
    Real.log (2161 : ℝ) ≤ Real.log (residueNormBase S2696GaussianPlace) :=
      S2699_log2161_le_log_residueNormBase
    _ = (1 : ℝ) * Real.log (residueNormBase S2696GaussianPlace) := (one_mul _).symm
    _ ≤ (parameter.order : ℝ) * Real.log (residueNormBase S2696GaussianPlace) :=
      mul_le_mul_of_nonneg_right horder hlogpos

theorem S2699_log2161_le_abs_log_q
    (parameter : FinitePlaceQCandidate S2696GaussianPlace) :
    Real.log (2161 : ℝ) ≤ |Real.log ‖parameter.q‖| := by
  change Real.log (2161 : ℝ) ≤ |localSignedLog parameter|
  rw [abs_localSignedLog]
  exact S2699_log2161_le_localLogMagnitude parameter

#check S2699_log2161_le_localLogMagnitude
#check S2699_log2161_le_abs_log_q
#print axioms S2699_log2161_le_localLogMagnitude
#print axioms S2699_log2161_le_abs_log_q

end LeanFormal.IUT.XiFPaper.S2699LogQ2161Actual
end
