/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Ob33B5IndexActual
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import tmp.sheaf.xif.paper.Mzk1B5FractionalCountNumDenActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual

/-!
# Route B #3: relativePlaceIndex <-> FractionalIdeal.count and placeLogVolume

Bridges the rank-one relative index of Mzk1Ob33B5IndexActual to the
FractionalIdeal.count exponent (qpilot bridge) and the mainline count/log
placeLogVolume theorem.  The remaining norm/valuation bridge inputs are explicit
hypotheses from Mzk1B5CountLocalValuationBridgeActual, not silently assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountBridgeActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1Ob33B5IndexActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FractionalCountNumDenActual

variable {k : Type} [Field k] [NumberField k]

/-- Numerator ideal count of a fractional ideal at a finite place. -/
noncomputable def fractionalNumCount
    (v : NumberField.FinitePlace k) (I : LineBundle (k := k)) : Int :=
  ((Associates.mk v.maximalIdeal.asIdeal).count (Associates.mk I.num).factors : Int)

/-- Denominator ideal count of a fractional ideal at a finite place. -/
noncomputable def fractionalDenCount
    (v : NumberField.FinitePlace k) (I : LineBundle (k := k)) : Int :=
  ((Associates.mk v.maximalIdeal.asIdeal).count
    (Associates.mk (Ideal.span {(I.den : NumberField.RingOfIntegers k)})).factors : Int)

/-- Relative index equals the negative count difference, from the count-valuation bridge. -/
theorem relativePlaceIndex_eq_neg_count_add_count
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v)
    (hvalH : CountValuationBridge (k := k) dH)
    (hvalO : CountValuationBridge (k := k) dO) :
    relativePlaceIndex dH dO =
      - (countExponent (k := k) v H : Int) + (countExponent (k := k) v O : Int) := by
  unfold relativePlaceIndex
  have hHval : PaperOModuleActual.localValuation (k := k) v dH.generator =
      - (countExponent (k := k) v H : Int) := hvalH
  have hOval : PaperOModuleActual.localValuation (k := k) v dO.generator =
      - (countExponent (k := k) v O : Int) := hvalO
  rw [hHval, hOval]
  ring

/-- Relative index expressed as numerator-minus-denominator counts of the two
fractional ideals (using the qpilot fractional count theorem). -/
theorem relativePlaceIndex_eq_num_den_counts
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (hH : H ≠ 0) (hO : O ≠ 0)
    (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v)
    (hvalH : CountValuationBridge (k := k) dH)
    (hvalO : CountValuationBridge (k := k) dO) :
    relativePlaceIndex dH dO =
      - (fractionalNumCount v H - fractionalDenCount v H) +
        (fractionalNumCount v O - fractionalDenCount v O) := by
  rw [relativePlaceIndex_eq_neg_count_add_count dH dO hvalH hvalO]
  unfold countExponent fractionalNumCount fractionalDenCount
  rw [Mzk1B5FractionalCountNumDenActual.count_eq_count_num_sub_count_den k H hH v.maximalIdeal,
    Mzk1B5FractionalCountNumDenActual.count_eq_count_num_sub_count_den k O hO v.maximalIdeal]

/-- Place log-volume difference equals the relative index times the residue norm
log (using the mainline placeLogVolume/count theorem). -/
theorem placeLogVolume_sub_eq_relativeIndex_mul_log_residueNormBase
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v)
    (dO : LocalGeneratorData (k := k) O v)
    (hvalH : CountValuationBridge (k := k) dH)
    (hvalO : CountValuationBridge (k := k) dO)
    (hnormH : LocalNormGeneratorBridge (k := k) dH)
    (hnormO : LocalNormGeneratorBridge (k := k) dO) :
    placeLogVolume dH - placeLogVolume dO =
      - ((relativePlaceIndex dH dO : Real) * Real.log (residueNormBase v)) := by
  rw [placeLogVolume_eq_count_mul_log_residueNormBase dH hvalH hnormH,
    placeLogVolume_eq_count_mul_log_residueNormBase dO hvalO hnormO]
  unfold relativePlaceIndex
  have hHval : PaperOModuleActual.localValuation (k := k) v dH.generator =
      - (countExponent (k := k) v H : Int) := hvalH
  have hOval : PaperOModuleActual.localValuation (k := k) v dO.generator =
      - (countExponent (k := k) v O : Int) := hvalO
  rw [hHval, hOval]
  push_cast
  ring

def countBridgeRows : List (String × String × String) :=
  [ ("fractionalNumCount/fractionalDenCount", "num/den ideal counts at v", "CONSTRUCTED"),
    ("relativePlaceIndex_eq_neg_count_add_count", "index = -countH + countO", "PROVED conditional on CountValuationBridge"),
    ("relativePlaceIndex_eq_num_den_counts", "index = num/den count differences (qpilot theorem)", "PROVED conditional"),
    ("placeLogVolume_sub_eq_relativeIndex_mul_log_residueNormBase", "place log difference = index * log residueNormBase", "PROVED conditional on count/norm bridges") ]

theorem countBridgeRows_length : countBridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33B5CountBridgeActual
