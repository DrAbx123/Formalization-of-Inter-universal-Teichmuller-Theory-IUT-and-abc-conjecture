/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5CountUnconditionalAttemptActual
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorValuationRelationActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountUnconditionalAttemptActual
variable {k : Type} [Field k] [NumberField k]
theorem countValuationBridge_iff_spanGeneratorValuation
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) :
    CountValuationBridge (k := k) d ↔
      PaperOModuleActual.localValuation (k := k) v d.generator =
        - (countExponent (k := k) v I : Int) := Iff.rfl
theorem localValuation_eq_neg_count_of_bridge
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (h : CountValuationBridge (k := k) d) :
    PaperOModuleActual.localValuation (k := k) v d.generator =
      - (countExponent (k := k) v I : Int) := h
end LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorValuationRelationActual
