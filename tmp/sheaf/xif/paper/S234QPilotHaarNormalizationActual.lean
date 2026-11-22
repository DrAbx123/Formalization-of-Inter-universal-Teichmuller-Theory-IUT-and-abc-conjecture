import Mathlib.MeasureTheory.Measure.Haar.Unique
/-! # S234: exact Haar normalization factor object
For two additive Haar measures on a locally compact second countable additive
group, Haar uniqueness gives the exact scalar `addHaarScalarFactor` such that
mu' = factor • mu.  This file constructs that actual factor object and proves
the exact proportionality.  The concrete qPilot pair instantiates it once the
two measures are known to be additive Haar; those instances are not fabricated.
No inequality. -/
noncomputable section
open scoped NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S234QPilotHaarNormalizationActual
open MeasureTheory
open MeasureTheory.Measure
universe u
variable {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
variable [SecondCountableTopology G]
variable (μ' μ : Measure G)
variable [Measure.IsAddHaarMeasure μ]
variable [IsFiniteMeasureOnCompacts μ']
variable [Measure.IsAddLeftInvariant μ']
/-- Exact Haar normalization factor of μ' relative to μ. -/
noncomputable def haarNormalizationFactor : ℝ≥0 :=
  μ'.addHaarScalarFactor μ
/-- Exact proportionality with the Haar normalization factor. -/
theorem haarNormalizationFactor_spec : μ' = (haarNormalizationFactor μ' μ) • μ :=
  isAddLeftInvariant_eq_smul μ' μ
/-- Actual exact normalization factor object. -/
structure HaarNormalizationFactorActual where
  factor : ℝ≥0
  factor_eq : factor = haarNormalizationFactor μ' μ
  proportional : μ' = factor • μ
/-- Actual factor object inhabitant. -/
noncomputable def haarNormalizationFactorActual :
    HaarNormalizationFactorActual μ' μ where
  factor := haarNormalizationFactor μ' μ
  factor_eq := rfl
  proportional := haarNormalizationFactor_spec μ' μ
/-- The concrete qPilot instantiation statement: once
the native/transported qPilot product measures are additive Haar, the exact
factor is their addHaarScalarFactor.  This is the exact type expected by the
concrete S232 pair. -/
def QPilotHaarNormalizationStatement : Prop :=
  ∀ {G : Type u} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (μ' μ : Measure G)
    [Measure.IsAddHaarMeasure μ] [IsFiniteMeasureOnCompacts μ']
    [Measure.IsAddLeftInvariant μ'],
      μ' = (μ'.addHaarScalarFactor μ) • μ
theorem QPilotHaarNormalizationStatement_actual :
    QPilotHaarNormalizationStatement :=
  fun μ' μ => isAddLeftInvariant_eq_smul μ' μ
end LeanFormal.IUT.XiFPaper.S234QPilotHaarNormalizationActual
