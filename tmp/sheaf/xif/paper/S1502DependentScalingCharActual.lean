import tmp.sheaf.xif.paper.S1422HDDDetActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

noncomputable section
open MeasureTheory
open scoped Pointwise BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.NumberFieldFinitePlace

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

/-- The actual product unit ball of the dependent local-field product. -/
noncomputable abbrev dependentUnitRegion (s : Finset (NumberField.FinitePlace ℚ)) :
    Set (dependentPoint s) :=
  unitRegion (K := S1402DependentE s)

/-- Exact first missing measure lemma: the diagonal prime-inverse unit scales
the additive product Haar measure of the unit ball by the product of the
residue characteristics.  No character identity is assumed. -/
def S1502ProductScalingMeasure (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  dependentHaar s (dependentPrimeUnit s • dependentUnitRegion s) =
    (dependentExponent s : ENNReal) * dependentHaar s (dependentUnitRegion s)

/-- Exact local first measure/character lemma at one dependent place: the
inverse residue characteristic has local Haar character equal to the residue
characteristic. -/
def S1502LocalPrimeScaling (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : Prop :=
  (distribHaarChar (S1402DependentE s v) (dependentPrimeInverseUnit s v) : ENNReal) =
    (dependentPlacePrime s v : ENNReal)

/-- The product scaling measure lemma implies the dependent character identity,
provided the unit ball has positive finite Haar mass. -/
theorem s1502DependentProductScalingChar_of_measure
    (s : Finset (NumberField.FinitePlace ℚ))
    (hscale : S1502ProductScalingMeasure s)
    (hpos : 0 < dependentHaar s (dependentUnitRegion s))
    (hfin : dependentHaar s (dependentUnitRegion s) < ⊤) :
    DependentProductScalingChar s := by
  unfold DependentProductScalingChar S1502ProductScalingMeasure at *
  have h := distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := dependentHaar s)
    (g := dependentPrimeUnit s)
    (s := dependentUnitRegion s)
    (r := (dependentExponent s : NNReal)) hpos.ne' hfin.ne ?_
  · simpa using congrArg (fun r : NNReal => (r : ENNReal)) h
  · simpa using hscale

/-- Exact first unresolved measure responsibility after S1422: product scaling
of the unit ball by the diagonal prime-inverse unit. -/
def S1502FirstMissingMeasureLemma (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  S1502ProductScalingMeasure s

end LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual

end
