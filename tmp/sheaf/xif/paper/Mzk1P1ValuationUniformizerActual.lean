/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import Mathlib.Tactic

/-! # P1: valuation of a uniformizer is -1 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1ValuationUniformizerActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

/-- Uniformizer value: localValuation of the uniformizer equals -1. -/
theorem valuation_uniformizer_eq_neg_one (v : NumberField.FinitePlace k)
    (pi : LocalRing (k := k) v)
    (hpi : Valued.v (pi : LocalField (k := k) v) = Multiplicative.ofAdd (-1 : Int)) :
    localValuation (k := k) v (pi : LocalField (k := k) v) = -1 := by
  show (Valued.v (pi : LocalField (k := k) v)).log = -1
  rw [hpi]
  rfl

def valuationUniformizerRows : List (String × String × String) :=
  [ ("valuation_uniformizer_eq_neg_one", "localValuation pi = -1", "PROVED") ]

theorem valuationUniformizerRows_length : valuationUniformizerRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1ValuationUniformizerActual

end
