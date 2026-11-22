import tmp.sheaf.xif.paper.S1520LocalCompletionHaarActual
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section
open MeasureTheory
open scoped Pointwise BigOperators ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1576ProductHaarDecompositionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual
open LeanFormal.IUT.NumberFieldFinitePlace

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

variable (s : Finset (NumberField.FinitePlace ℚ))

local instance localDependentHaarIsAddHaar
    (v : {v // v ∈ s}) :
    Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (S1402DependentE s v)) :=
  Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)

/-- The local product Haar measure on the dependent product. -/
noncomputable def productLocalHaar :
    Measure (dependentPoint s) :=
  Measure.pi (fun v : {v // v ∈ s} =>
    (Measure.addHaar : Measure (S1402DependentE s v)))

/-- The product of local additive Haar measures is an additive Haar measure. -/
noncomputable instance productLocalHaarIsAddHaar :
    Measure.IsAddHaarMeasure (productLocalHaar s) := by
  unfold productLocalHaar
  exact Measure.pi.isAddHaarMeasure _

/-- Exact product measure decomposition: the canonical dependent Haar is a
nonzero finite scalar multiple of the product of local additive Haar measures. -/
theorem s1576ProductHaarDecomposition :
    S1512ProductHaarDecomposition s := by
  let ν := productLocalHaar s
  haveI : Measure.IsAddHaarMeasure ν := productLocalHaarIsAddHaar s
  haveI : Measure.IsAddHaarMeasure (dependentHaar s) :=
    Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)
  refine ⟨((Measure.addHaarScalarFactor (dependentHaar s) ν : NNReal) : ENNReal), ?_, ?_, ?_⟩
  · exact_mod_cast (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (dependentHaar s) ν).ne'
  · exact ENNReal.coe_ne_top
  · exact Measure.isAddLeftInvariant_eq_smul (dependentHaar s) ν

/-- Exact next measure lemma: the product of local unit balls scales by the
product of the local residue characteristics under the diagonal prime-inverse
unit. -/
def S1576ProductUnitBallScaling : Prop :=
  productLocalHaar s (dependentPrimeUnit s • dependentUnitRegion s) =
    (dependentExponent s : ENNReal) *
      productLocalHaar s (dependentUnitRegion s)

/-- The product unit-ball scaling and the product measure decomposition give
S1502's product scaling measure. -/
theorem s1576ProductScalingMeasure_of_unitBallScaling
    (h : S1576ProductUnitBallScaling s) :
    S1502ProductScalingMeasure s := by
  unfold S1502ProductScalingMeasure
  obtain ⟨c, _hc0, _hctop, hdecomp⟩ := s1576ProductHaarDecomposition s
  have h1 := congrArg
    (fun μ : Measure (dependentPoint s) =>
      μ (dependentPrimeUnit s • dependentUnitRegion s)) hdecomp
  have h2 := congrArg
    (fun μ : Measure (dependentPoint s) => μ (dependentUnitRegion s)) hdecomp
  simp only [Measure.smul_apply, smul_eq_mul] at h1 h2
  rw [h1, h2]
  change c * productLocalHaar s
      (dependentPrimeUnit s • dependentUnitRegion s) =
    (dependentExponent s : ENNReal) *
      (c * productLocalHaar s (dependentUnitRegion s))
  rw [h]
  conv_lhs => rw [← mul_assoc]
  conv_rhs => rw [← mul_assoc]
  rw [mul_comm c (dependentExponent s : ENNReal)]

end LeanFormal.IUT.XiFPaper.S1576ProductHaarDecompositionActual

end
