/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.NativeBadLiftActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4FKDescentBridge
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.Tactic

/-!
# P6-B4: QPLACE choice-gap interface (single declaration cluster)

Status: CONDITIONAL/GAP.  The literal equality `sectionFiniteLift (K-place) =
nativeBadLift.lift (F-place)` is ill-typed; the same-carrier form is
`fkDescentShadow = nativeBadLift.lift`.  The comap equality is PROVED; the
place equality is a named gap because both sides are different
`Classical.choose` values.  No sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1C17QPLACEChoiceGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Same-carrier QPLACE: the F-shadow of the section K-place equals the
lying-over F-place. -/
def QPlaceChoiceGap : Prop :=
  fkDescentShadow (nativePlaceSelection T) b.1 = (nativeBadLift T).lift b

/-- The common contraction (PROVED): both F-places lie over the same moduli place. -/
theorem qplace_comap_eq :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (fkDescentShadow (nativePlaceSelection T) b.1) =
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b) := by
  rw [fkDescentShadow_comap, (nativeBadLift T).lift_comap]

/-- QPLACE implies the comap equality (proved, but not the converse). -/
theorem qplace_imp_comap (h : QPlaceChoiceGap T b) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (fkDescentShadow (nativePlaceSelection T) b.1) =
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b) := by
  simpa [h] using qplace_comap_eq T b

def qplaceRows : List (String × String × String) :=
  [ ("QPlaceChoiceGap", "fkDescentShadow = nativeBadLift.lift (F-place)", "GAP (Prop, choice)"),
    ("qplace_comap_eq", "same contraction", "PROVED"),
    ("qplace_imp_comap", "QPLACE => comap equality", "PROVED (one direction)") ]

theorem qplaceRows_length : qplaceRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1C17QPLACEChoiceGapActual
