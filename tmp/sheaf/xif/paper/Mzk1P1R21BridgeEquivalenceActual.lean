/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1R21BridgeActual
import tmp.sheaf.xif.paper.Mzk1P1GeneratorValuationRelationActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeEquivalenceActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorValuationRelationActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
variable {k : Type} [Field k] [NumberField k]
theorem r21Bridge_iff_countValuationBridge
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) :
    R21Bridge (k := k) d ↔ CountValuationBridge (k := k) d := Iff.rfl
theorem r21Bridge_of_countValuationBridge
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (h : CountValuationBridge (k := k) d) : R21Bridge (k := k) d := h
def R21CountBridgeInput (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v), CountValuationBridge (k := k) d
theorem r21ReductionTarget_of_countBridge
    (h : R21CountBridgeInput k) : R21ReductionTarget (k := k) := by
  intro _ I v d
  exact h d
end LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeEquivalenceActual
