/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-! # P1: B5 output with the residue degree `f_v` -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1B5WithFvActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual

variable {k : Type} [Field k] [NumberField k]

/-- B5 with the residue degree: place log-volume difference equals the valuation
difference times `f_v log p`. -/
def PlaceB5WithFv {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v) (dO : LocalGeneratorData (k := k) O v)
    (vH vO : Int) (fv : Nat) : Prop :=
  placeLogVolume dH - placeLogVolume dO =
    - (((vH - vO : Int) : Real)) * (fv : Real) *
      Real.log (NumberFieldFinitePlace.residueCharacteristic v : Real)

theorem placeB5WithFv_of_target
    {H O : LineBundle (k := k)} {v : NumberField.FinitePlace k}
    (dH : LocalGeneratorData (k := k) H v) (dO : LocalGeneratorData (k := k) O v)
    (vH vO : Int) (fv : Nat)
    (hB5 : PlaceB5Target (k := k) dH dO vH vO
      ((fv : Real) * Real.log (NumberFieldFinitePlace.residueCharacteristic v : Real))) :
    PlaceB5WithFv (k := k) dH dO vH vO fv := by
  unfold PlaceB5WithFv
  unfold PlaceB5Target at hB5
  rw [hB5]
  ring

def b5WithFvRows : List (String × String × String) :=
  [ ("PlaceB5WithFv", "B5 with residue degree f_v", "DEF"),
    ("placeB5WithFv_of_target", "from PlaceB5Target with logp = f_v log residueCharacteristic", "PROVED") ]

theorem b5WithFvRows_length : b5WithFvRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1B5WithFvActual

end