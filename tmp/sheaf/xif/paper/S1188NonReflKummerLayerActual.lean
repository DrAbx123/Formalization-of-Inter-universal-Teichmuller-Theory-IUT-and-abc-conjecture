import tmp.sheaf.xif.paper.S1187NonReflKummerCommonGroupActual

/-! # S1188: non-refl common-group Kummer layer

Packages the S1187 graph-group Kummer isomorphism into the production
SourceTimesMuKummerLayer, so S1195 can build the actual non-refl upperEnv.
Consumer: S1195ActualUpperEnv.upperEnvLayer / upperEnv. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1188NonReflKummerLayerActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual

universe umon uv upi
variable {V : Type uv}
variable {upper lower : FPrimeStrip.{umon, uv, upi} V}
variable [∀ v : V, TopologicalSpace (upper.Pi v)]

/-- Actual non-refl Kummer layer on the graph common group. -/
noncomputable def nonreflKummerLayer
    (φ : FPrimeStripEquiv upper lower) :
    SourceTimesMuKummerLayer (GraphGroup (upper := upper)) upper lower where
  sourceAction := fun v => (upper.unitsAction v).comp (factorUpper v)
  targetAction := fun v => (lower.unitsAction v).comp (factorLower φ v)
  kummer := fun v => kummerIsoAt φ v

/-- The unit portion extracted from the non-refl layer. -/
noncomputable def nonreflUnitPortion
    (φ : FPrimeStripEquiv upper lower) :
    SourceEvaluationUnitPortion (GraphGroup (upper := upper)) upper lower :=
  SourceEvaluationUnitPortion.ofKummerLayer (nonreflKummerLayer φ)

/-- Actual non-refl evaluation arrow from the graph layer. -/
noncomputable def nonreflEvaluationArrow
    (φ : FPrimeStripEquiv upper lower) :
    SourceEvaluationArrow (GraphGroup (upper := upper)) upper lower :=
  sourceEvaluationArrowOfUnitPortion φ (nonreflUnitPortion φ)

end LeanFormal.IUT.XiFPaper.S1188NonReflKummerLayerActual
end