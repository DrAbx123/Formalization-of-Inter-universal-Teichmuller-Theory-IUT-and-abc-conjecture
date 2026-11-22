/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1LocalizedLineIdealMapActual
import tmp.sheaf.xif.paper.Mzk1P1SpanGeneratorValuationMaxIdealActual
import tmp.sheaf.xif.paper.Mzk1P1GeneratorCountActual
import tmp.sheaf.xif.paper.Mzk1P1CountSideMaxIdealActual
import Mathlib.Tactic

/-! # P1: max-ideal CountValuationBridge / R21Bridge, unconditional -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1MaxIdealR21UncondActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual
open LeanFormal.IUT.XiFPaper.Mzk1P1LocalizedLineIdealMapActual
open LeanFormal.IUT.XiFPaper.Mzk1P1SpanGeneratorValuationMaxIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1CountSideMaxIdealActual

variable {k : Type} [Field k] [NumberField k]

/-- Generator datum for the max-ideal line from an explicit uniformizer and the span
identification of the localized line. -/
noncomputable def maxIdealGeneratorData (v : NumberField.FinitePlace k)
    (pi : LocalRing (k := k) v)
    (hspan : localizedLine (k := k) ((((underlyingPrime v).asIdeal : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k))) v =
      Submodule.span (LocalRing (k := k) v) {(pi : LocalField (k := k) v)}) :
    LocalGeneratorData (k := k) ((((underlyingPrime v).asIdeal : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k))) v :=
  { generator := (pi : LocalField (k := k) v)
    span_eq := hspan }

/-- Unconditional max-ideal CountValuationBridge. -/
theorem maxIdeal_countValuationBridge_uncond (v : NumberField.FinitePlace k) :
    exists d : LocalGeneratorData (k := k) ((((underlyingPrime v).asIdeal : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k))) v,
      CountValuationBridge (k := k) d := by
  obtain ⟨pi, hpi, hspan⟩ := localizedLine_maxIdeal_eq_span_uniformizer (k := k) v
  refine ⟨maxIdealGeneratorData (k := k) v pi hspan, ?_⟩
  exact countValuationBridge_maxIdeal_of_generator (k := k) v
    (maxIdealGeneratorData (k := k) v pi hspan) pi rfl hpi

/-- Unconditional max-ideal R21Bridge. -/
theorem maxIdeal_r21Bridge_uncond (v : NumberField.FinitePlace k) :
    exists d : LocalGeneratorData (k := k) ((((underlyingPrime v).asIdeal : Ideal (NumberField.RingOfIntegers k)) : LineBundle (k := k))) v,
      R21Bridge (k := k) d := by
  obtain ⟨pi, hpi, hspan⟩ := localizedLine_maxIdeal_eq_span_uniformizer (k := k) v
  refine ⟨maxIdealGeneratorData (k := k) v pi hspan, ?_⟩
  exact r21Bridge_maxIdeal_of_generator (k := k) v
    (maxIdealGeneratorData (k := k) v pi hspan) pi rfl hpi

def maxIdealR21UncondRows : List (String × String × String) :=
  [ ("maxIdeal_countValuationBridge_uncond", "max-ideal CountValuationBridge, unconditional", "PROVED"),
    ("maxIdeal_r21Bridge_uncond", "max-ideal R21Bridge, unconditional", "PROVED") ]

theorem maxIdealR21UncondRows_length : maxIdealR21UncondRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1MaxIdealR21UncondActual

end