/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapPowerGeneralProofActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedLineIdealMapActual
import tmp.sheaf.xif.paper.Mzk1P1UniformizerPowerSpanActual
import Mathlib.Tactic

/-! # P1: IdealLocalizedCountStatement from the three bridges (unconditional) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountFinalActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineIdealMapActual
open LeanFormal.IUT.XiFPaper.Mzk1P1UniformizerPowerSpanActual

variable {k : Type} [Field k] [NumberField k]

/-- `IdealLocalizedCountStatement` is now unconditional: all three bridge hypotheses
are proved (general ideal-map power, bridge 2 span identity, uniformizer power span). -/
theorem idealLocalizedCountStatement_proved
    (I : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0)
    (v : NumberField.FinitePlace k) :
    IdealLocalizedCountStatement I hI v :=
  idealLocalizedCount_of_bridges I hI v
    (idealMapPowerStatement_general I hI v)
    (by
      change localizedLine (k := k) (I : LineBundle (k := k)) v =
        Submodule.span (LocalRing (k := k) v)
          ((fun x : LocalRing (k := k) v => (x : LocalField (k := k) v)) ''
            ((Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v)) I :
              Ideal (LocalRing (k := k) v)) : Set (LocalRing (k := k) v)))
      exact localizedLine_eq_span_idealMap I v)
    (uniformizerPowerSpan_proved v)

def localizedCountFinalRows : List (String × String × String) :=
  [ ("idealLocalizedCountStatement_proved", "IdealLocalizedCountStatement unconditional (3 bridges)", "PROVED") ]

theorem localizedCountFinalRows_length : localizedCountFinalRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountFinalActual

end