/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1SpanGeneratorValuationMaxIdealActual
import tmp.sheaf.xif.paper.Mzk1P1R21BridgeEquivalenceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeMaxIdealCountActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1CountSideMaxIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1SpanGeneratorValuationMaxIdealActual
open LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeEquivalenceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem r21Bridge_maxIdeal_count
    (v : NumberField.FinitePlace k)
    (d : LocalGeneratorData (k := k)
      ((v.maximalIdeal.asIdeal : LineBundle (k := k))) v)
    (pi : LocalRing (k := k) v)
    (hgen : d.generator = (pi : LocalField (k := k) v))
    (hpi : Valued.v (pi : LocalField (k := k) v) =
      Multiplicative.ofAdd (-1 : Int)) :
    R21Bridge d :=
  r21Bridge_of_countValuationBridge d
    (countValuationBridge_maxIdeal_of_generator v d pi hgen hpi)


end LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeMaxIdealCountActual
