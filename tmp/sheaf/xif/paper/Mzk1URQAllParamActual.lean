/- D2 Q_all interface (kurt): parameterized q-pilot magnitude over a Finset of bad
places, with the monotone subset relation giving the per-place Q <= h direction.
The full index set of the paper's Q_all is still awaiting the Lead ruling (route
L577-590); this file deliberately keeps it parametric (no faked object).

THIS FILE ONLY uses maxHeartbeats 1000000 (paper-level budget). -/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URQAllParamActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The log p letter is nonnegative. -/
theorem ksLogP_nonneg (b : Bad (nativePlaceSelection T)) : 0 ≤ ksLogP T b := by
  unfold ksLogP
  apply Real.log_nonneg
  have hp : Nat.Prime ((completionRationalPrime (nativeBadToKPlace T b)).val) :=
    (Fact.out : Nat.Prime ((completionRationalPrime (nativeBadToKPlace T b)).val))
  exact_mod_cast hp.one_lt.le

/-- The q-pilot magnitude over a selected Finset of bad places, with weights w. -/
noncomputable def qPilotMagnitudeOn (w : Bad (nativePlaceSelection T) → ℝ)
    (s : Finset (Bad (nativePlaceSelection T))) : ℝ :=
  ∑ b ∈ s, w b * (qVFamNormalizedCoefficient T b * ksLogP T b)

/-- The paper q-pilot magnitude is the full-bad-place instance. -/
theorem qPilotMagnitudePaper_eq_univ :
    qPilotMagnitudePaper (l := l) T =
      qPilotMagnitudeOn (l := l) T (normDegreeWeight T) Finset.univ := by
  unfold qPilotMagnitudePaper qPilotMagnitudeOn
  simp

/-- Each term of the q-pilot sum is nonnegative. -/
theorem qPilotMagnitude_term_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ normDegreeWeight T b * (qVFamNormalizedCoefficient T b * ksLogP T b) := by
  refine mul_nonneg (normDegreeWeight_nonneg (l := l) T b)
    (mul_nonneg (qVFamNormalizedCoefficient_nonneg T b) (ksLogP_nonneg T b))

/-- Subset monotonicity: the selected Q is at most the full-bad-place Q. -/
theorem qPilotMagnitudeOn_le_univ (w : Bad (nativePlaceSelection T) → ℝ)
    (hw : ∀ b, 0 ≤ w b) (s : Finset (Bad (nativePlaceSelection T))) :
    qPilotMagnitudeOn (l := l) T w s ≤ qPilotMagnitudeOn (l := l) T w Finset.univ := by
  unfold qPilotMagnitudeOn
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
  intro b _ _
  exact mul_nonneg (hw b)
    (mul_nonneg (qVFamNormalizedCoefficient_nonneg T b) (ksLogP_nonneg T b))

/-- The specific selection Q <= h at the current weight family (per-place version). -/
theorem qPilotMagnitudePaper_le_univ
    (s : Finset (Bad (nativePlaceSelection T))) :
    qPilotMagnitudeOn (l := l) T (normDegreeWeight T) s ≤
      qPilotMagnitudePaper (l := l) T := by
  rw [qPilotMagnitudePaper_eq_univ (l := l) T]
  exact qPilotMagnitudeOn_le_univ (l := l) T (normDegreeWeight T)
    (normDegreeWeight_nonneg (l := l) T) s

#print axioms ksLogP_nonneg
#print axioms qPilotMagnitudePaper_eq_univ
#print axioms qPilotMagnitudeOn_le_univ

end LeanFormal.IUT.XiFPaper.Mzk1URQAllParamActual
end