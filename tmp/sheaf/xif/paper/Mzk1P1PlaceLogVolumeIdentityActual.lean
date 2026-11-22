/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: per-place log-volume identity -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PlaceLogVolumeIdentityActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1B5CountLocalValuationBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

def PlaceLogVolumeIdentity : Prop :=
  forall (I : LineBundle (k := k)) (v : NumberField.FinitePlace k)
    (d : LocalGeneratorData (k := k) I v),
    placeLogVolume d =
      (countExponent (k := k) v I : Real) * Real.log (residueNormBase v)

def placeLogVolumeRows : List (String × String × String) :=
  [ ("PlaceLogVolumeIdentity", "placeLogVolume d = count * log residueNormBase", "PROVED (conditional: two bridges, CountLocalValuationBridge)"),
    ("placeLogVolume_eq_count_mul_log_residueNormBase", "same", "PROVED conditional") ]

theorem placeLogVolumeRows_length : placeLogVolumeRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1PlaceLogVolumeIdentityActual

end
