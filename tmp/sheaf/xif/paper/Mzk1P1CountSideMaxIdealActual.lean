/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import tmp.sheaf.xif.paper.Mzk1P1R21BridgeEquivalenceActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import tmp.sheaf.xif.paper.Mzk1P1GeneratorCountActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountSideMaxIdealActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1R21BridgeEquivalenceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1GeneratorCountActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem countExponent_self_maxIdeal (v : NumberField.FinitePlace k) :
    countExponent (k := k) v ((v.maximalIdeal.asIdeal : LineBundle (k := k))) = 1 := by
  unfold countExponent
  exact FractionalIdeal.count_self (K := k) (v := v.maximalIdeal)
theorem localValuation_uniformizer (v : NumberField.FinitePlace k)
    (pi : LocalRing (k := k) v)
    (hpi : Valued.v (pi : LocalField (k := k) v) =
      Multiplicative.ofAdd (-1 : Int)) :
    localValuation v (pi : LocalField (k := k) v) = -1 := by
  unfold localValuation
  rw [hpi]
  simpa [WithZero.exp, Multiplicative.ofAdd] using (WithZero.log_exp (-1 : Int))
theorem countValuationBridge_maxIdeal_of_generator
    (v : NumberField.FinitePlace k)
    (d : LocalGeneratorData (k := k)
      ((v.maximalIdeal.asIdeal : LineBundle (k := k))) v)
    (pi : LocalRing (k := k) v)
    (hgen : d.generator = (pi : LocalField (k := k) v))
    (hpi : Valued.v (pi : LocalField (k := k) v) =
      Multiplicative.ofAdd (-1 : Int)) :
    CountValuationBridge (k := k) d := by
  unfold CountValuationBridge
  rw [hgen, localValuation_uniformizer v pi hpi, countExponent_self_maxIdeal]
theorem r21Bridge_maxIdeal_of_generator
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
end LeanFormal.IUT.XiFPaper.Mzk1P1CountSideMaxIdealActual
