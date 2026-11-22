/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual

/-! # Route B #3: count <-> localValuation / placeLogVolume bridge

Bridges the fractional-ideal exponent `countExponent v I` (FractionalIdeal.count)
with the local valuation `localValuation v` of DeterminantLogVolumeActual and the
generator-based `placeLogVolume` of Mzk1DetLinePlaceB5Actual.

Exact content inputs (Mathlib gaps recorded, not assumed):
* LocalNormGeneratorBridge: log ||x|| = localValuation(v,x) * log(residueNormBase v)
  (the local norm/valuation compatibility at the actual place);
* residue degree one: log(residueNormBase v) = log(residueCharacteristic v)
  (needed to compare with the paper localLogVolume which uses the rational prime).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

variable {k : Type} [Field k] [NumberField k]

/-- Named input: the local norm of the generator is its valuation times log(residueNormBase). -/
def LocalNormGeneratorBridge {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) : Prop :=
  Real.log ‖d.generator‖ =
    (localValuation (k := k) v d.generator : Real) *
      Real.log (residueNormBase v)

/-- Named input: the generator valuation is minus the fractional-ideal exponent. -/
def CountValuationBridge {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v) : Prop :=
  localValuation (k := k) v d.generator =
    - (countExponent (k := k) v I : Int)

/-- Generator place log-volume = count * log(residueNormBase), from the two bridges. -/
theorem placeLogVolume_eq_count_mul_log_residueNormBase
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (hval : CountValuationBridge (k := k) d)
    (hnorm : LocalNormGeneratorBridge (k := k) d) :
    placeLogVolume d =
      (countExponent (k := k) v I : Real) * Real.log (residueNormBase v) := by
  unfold placeLogVolume
  rw [hnorm, hval]
  push_cast
  ring

/-- Same, compared with the paper localLogVolume (which uses the rational prime). -/
theorem placeLogVolume_eq_localLogVolume
    {I : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (d : LocalGeneratorData (k := k) I v)
    (hval : CountValuationBridge (k := k) d)
    (hnorm : LocalNormGeneratorBridge (k := k) d)
    (hchar : Real.log (residueNormBase v) =
      Real.log (NumberFieldFinitePlace.residueCharacteristic v : Real)) :
    placeLogVolume d = localLogVolume (k := k) v d.generator := by
  rw [placeLogVolume_eq_count_mul_log_residueNormBase d hval hnorm, hchar]
  unfold localLogVolume
  rw [hval]
  push_cast
  ring

def countValuationRows : List (String × String × String) :=
  [ ("LocalNormGeneratorBridge", "log ||x|| = localValuation * log(residueNormBase)", "GAP (named input)"),
    ("CountValuationBridge", "localValuation generator = -countExponent", "GAP (named input)"),
    ("placeLogVolume_eq_count_mul_log_residueNormBase", "placeLogVolume = count * log residueNormBase", "PROVED (conditional)"),
    ("placeLogVolume_eq_localLogVolume", "same with paper localLogVolume (needs residue degree one)", "PROVED (conditional)"),
    ("residue degree one", "log residueNormBase = log residueCharacteristic", "GAP (GAP-PC-RESDEG / tame)") ]

theorem countValuationRows_length : countValuationRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual

end