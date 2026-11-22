/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C17QPLACEChoiceGapActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.Tactic

/-! # P6-C4: QPLACE under F-place uniqueness (single cluster, CONDITIONAL) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1C17QPLACEChoiceGapActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QPLACELiftUniqueActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- k=1-style uniqueness input: every F-place over b.1 is the native lift. -/
def PlaceLiftUnique : Prop :=
  forall place : NumberField.FinitePlace T.arithmetic.F,
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) place = b.1 ->
      place = (nativeBadLift T).lift b

/-- If the F-lift is unique, QPLACE holds. -/
theorem qplace_of_liftUnique (h : PlaceLiftUnique T b) :
    QPlaceChoiceGap T b := by
  unfold QPlaceChoiceGap
  exact h (fkDescentShadow (nativePlaceSelection T) b.1)
    (fkDescentShadow_comap (nativePlaceSelection T) b.1)

def liftUniqueRows : List (String × String × String) :=
  [ ("PlaceLiftUnique", "all F-places over b.1 equal native lift", "CONDITIONAL input"),
    ("qplace_of_liftUnique", "uniqueness => QPLACE", "PROVED conditional") ]
theorem liftUniqueRows_length : liftUniqueRows.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QPLACELiftUniqueActual
