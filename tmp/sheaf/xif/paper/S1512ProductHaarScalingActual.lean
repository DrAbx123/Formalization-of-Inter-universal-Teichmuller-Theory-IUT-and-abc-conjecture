import tmp.sheaf.xif.paper.S1502DependentScalingCharActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

noncomputable section
open MeasureTheory
open scoped Pointwise BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.NumberFieldFinitePlace

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

/-- Exact local first measure/character lemma at one dependent place: the
inverse residue characteristic has local additive Haar character equal to the
residue characteristic. -/
abbrev S1512LocalCompletionScaling (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : Prop :=
  S1502LocalPrimeScaling s v

/-- Exact product measure decomposition: the canonical additive Haar on the
dependent product is a nonzero scalar multiple of the product of the local
additive Haar measures. -/
def S1512ProductHaarDecomposition (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  ∃ c : ENNReal,
    c ≠ 0 ∧ c ≠ ⊤ ∧
      dependentHaar s =
        c • Measure.pi (fun v : {v // v ∈ s} =>
          (Measure.addHaar : Measure (S1402DependentE s v)))

/-- Exact first missing measure lemma: local prime-inverse Haar scaling at a
dependent place. -/
def S1512FirstMissingMeasureLemma (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : Prop :=
  S1512LocalCompletionScaling s v

-- Donor checks.
#check LeanFormal.IUT.FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
#check s1502DependentProductScalingChar_of_measure

end LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual

end
