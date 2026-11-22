/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountValuationSignActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
variable {k : Type} [Field k] [NumberField k]
theorem localValuation_neg_of_count_pos
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (h : CountValuationBridge (k := k) d)
    (hc : 0 < countExponent v I) :
    localValuation v d.generator < 0 := by
  have hval : localValuation v d.generator =
      - (countExponent v I : Int) := h
  rw [hval]
  omega
theorem localValuation_pos_of_count_neg
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (h : CountValuationBridge (k := k) d)
    (hc : countExponent v I < 0) :
    0 < localValuation v d.generator := by
  have hval := h
  rw [hval]
  omega
end LeanFormal.IUT.XiFPaper.Mzk1P1CountValuationSignActual
