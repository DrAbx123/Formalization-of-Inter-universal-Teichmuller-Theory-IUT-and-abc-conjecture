import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.NativeC3

/-!
# EtaValueGroupLineActual

ETA-5 base object: the actual value-group real line `Rval` together with the
native q-pilot and its selected places.

`Rval = Multiplicative ℝ` is the actual real value-group target (not a
trivialized common real line).  The pilot is the actual native q-pilot
Kummer-relative log volume at the actual selected native places.  It is
nonzero because `qPilotSignedLog` is negative.

No Q/hull comparison and no trivialization are used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaValueGroupLineActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual value-group real line. -/
abbrev Rval : Type := Multiplicative ℝ

/-- Native q-pilot in `Rval`, from the actual q Kummer-relative log volume. -/
noncomputable def etaPilot : Rval :=
  Multiplicative.ofAdd (qPilotKummerRelativeVolume X)

/-- The actual selected native places used by the pilot. -/
def etaSelectedPlaces : Finset (NumberField.FinitePlace X.S.arithmetic.F) :=
  qPilotSelectedPlaces X

theorem etaSelectedPlaces_eq :
    etaSelectedPlaces X = qPilotSelectedPlaces X := rfl

theorem etaSelectedPlaces_nonempty :
    (etaSelectedPlaces X).Nonempty :=
  qPilotSelectedPlaces_nonempty X

/-- The pilot is non-trivial: its additive log is negative. -/
theorem etaPilot_ne_one : etaPilot X ≠ 1 := by
  have hneg : qPilotKummerRelativeVolume X < 0 := by
    rw [qPilotKummerRelativeVolume_eq]
    exact qPilotSignedLog_neg X
  intro h
  have hzero : qPilotKummerRelativeVolume X = 0 := by
    simpa [etaPilot] using congrArg Multiplicative.toAdd h
  linarith

/-- Actual ETA-5 value-group line data: Rval, non-trivial pilot, selected
native places, with the exact native q relations. -/
structure EtaValueGroupLineData (X : N8NativeInput l) where
  /-- Actual selected native places. -/
  selectedPlaces : Finset (NumberField.FinitePlace X.S.arithmetic.F)
  selectedPlaces_eq : selectedPlaces = qPilotSelectedPlaces X
  /-- Actual pilot in the real value-group line. -/
  pilot : Rval
  pilot_eq : pilot = Multiplicative.ofAdd (qPilotKummerRelativeVolume X)
  pilot_ne_one : pilot ≠ 1

/-- Actual construction of the ETA-5 value-group line. -/
noncomputable def etaValueGroupLineData :
    EtaValueGroupLineData X where
  selectedPlaces := qPilotSelectedPlaces X
  selectedPlaces_eq := rfl
  pilot := etaPilot X
  pilot_eq := rfl
  pilot_ne_one := etaPilot_ne_one X

theorem etaValueGroupLineData_nonempty :
    Nonempty (EtaValueGroupLineData X) :=
  ⟨etaValueGroupLineData X⟩

end LeanFormal.IUT.N8Closure.EtaValueGroupLineActual