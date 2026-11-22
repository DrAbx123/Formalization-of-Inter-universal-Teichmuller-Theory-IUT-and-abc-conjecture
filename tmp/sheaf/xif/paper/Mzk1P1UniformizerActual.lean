/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.external.ported.flt.FLT.DedekindDomain.AdicValuation
import Mathlib.Tactic

/-! # P1: uniformizer of the completed DVR (from FLT) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1UniformizerActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open Multiplicative

variable {k : Type} [Field k] [NumberField k]

/-- Existence of a uniformizer in the completed DVR. -/
def UniformizerData (v : NumberField.FinitePlace k) : Prop :=
  exists pi : LocalRing (k := k) v,
    Valued.v (pi : LocalField (k := k) v) = ofAdd (-1 : Int)

/-- FLT gives the uniformizer. -/
theorem uniformizerData_proved (v : NumberField.FinitePlace k) :
    UniformizerData (k := k) v := by
  obtain ⟨pi, hpi⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
    (K := k) (v := underlyingPrime v)
  exact ⟨pi, hpi⟩

def uniformizerRows : List (String × String × String) :=
  [ ("UniformizerData", "exists uniformizer with Valued.v = ofAdd(-1)", "DEF"),
    ("uniformizerData_proved", "FLT exists_uniformizer", "PROVED") ]

theorem uniformizerRows_length : uniformizerRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1UniformizerActual

end
