import tmp.sheaf.n8.closure.PaperC4IndBridgeActualAttempt
import tmp.sheaf.n8.closure.SourceAllowedActualDataReduction
import tmp.sheaf.n8.closure.P6Bridge

/-!
# C4 IndActionData actual attempt

Target: IndActionData on the old bridge output carrier with label group
Multiplicative (finiteLabel l).

Actual C4 carrier: C4.ind is literally an IndActionData for the C4 label group,
so c4IndActionDataOfC4 is actual and uses no arbitrary action.

Old bridge carrier: P6BridgeDonors gives the old input/binding and C1 place, but
no C4 record and no C4.ind; PaperLabelIndData only acts on the finite label set,
not on ThetaPilotPoint.  Hence the old-carrier IndActionData is not constructed
from those donors; the exact named gap is oldIndActionData_obligation.

No arbitrary action or free Ind field is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4IndActionDataActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
open LeanFormal.IUT.N8Closure.SourceAllowedActualDataReduction
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- C1 place data from the exact bridge binding. -/
noncomputable def oldPlaceData (D : P6BridgeDonors X) :
    C1PlaceData (I := (actualBridge D).input) where
  v := (actualBridge D).binding.place.selected
  R := (actualBridge D).binding.place.selected_realization

/-- Old bridge output carrier. -/
abbrev OldOutputCarrier (D : P6BridgeDonors X) : Type _ :=
  (actualBridge D).input.ThetaPilotPoint (oldPlaceData D).v

/-- Exact old-carrier IndActionData target with LAdd = finiteLabel l. -/
abbrev OldIndActionData (D : P6BridgeDonors X) : Type _ :=
  IndActionData (OldOutputCarrier D) (Multiplicative (finiteLabel l))

/-- Actual IndActionData on the C4 carrier: C4.ind itself, no arbitrary action. -/
noncomputable def c4IndActionDataOfC4
    {V : Type uv} (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I
      (Multiplicative (finiteLabel l))) :
    IndActionData (I.ThetaPilotPoint C4.place.v)
      (Multiplicative (finiteLabel l)) :=
  C4.ind

/-- Exact no-go record: the old carrier has no C4.ind, while PaperLabelIndData
acts only on finiteLabel; the missing bridge is the named gap. -/
def OldIndActionDataMissing (D : P6BridgeDonors X) : Prop :=
  Nonempty (OldIndActionData D)

end LeanFormal.IUT.N8Closure.C4IndActionDataActualAttempt
