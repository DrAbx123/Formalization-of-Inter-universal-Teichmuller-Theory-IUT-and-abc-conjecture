import tmp.sheaf.xif.paper.S827PaperValueGroupNormCardActual
/-! # S836: audit of the GeneralNormalizedNormBySpectralUniqueness dependency fix
The analytic formula file GeneralNormalizedNormBySpectralUniqueness is actual,
but its dependency BaseScalarValuationRelation does not compile in this
environment.  Fix items are recorded exactly; no fake norm formula. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S836NormFormulaFixAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S827PaperValueGroupNormCardActual
/-- Exact fix items required before the frozen card can be proved. -/
structure NormFormulaFixSpec where
  scalarField_universe : Prop
  pNat_coercion_alignment : Prop
  padicScalar_instance_alignment : Prop
  padicUnit_norm_one_available : Prop
  zpow_api_alignment : Prop
  completionField_algebraMap : Prop
/-- The actual analytic source that must be compiled after the fixes. -/
def AnalyticFormulaSource : String :=
  "LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean"
/-- Exact remaining formula source files. -/
def NormFormulaDependencyChain : List String := [
  "LeanFormal/IUT/Foundations/AlgebraicGeometry/BaseScalarValuationRelation.lean",
  "LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean",
  "LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormFinal.lean",
  "LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormConsumer.lean"]
end LeanFormal.IUT.XiFPaper.S836NormFormulaFixAuditActual
