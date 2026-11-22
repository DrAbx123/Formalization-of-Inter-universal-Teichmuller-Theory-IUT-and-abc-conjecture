import tmp.sheaf.n8.closure.C4IndActionDataActualAttempt
import tmp.sheaf.n8.closure.P6Bridge

/-!
# C4 old-carrier IndActionData transport attempt

The old carrier is

  OldOutputCarrier D = (actualBridge D).input.ThetaPilotPoint (oldPlaceData D).v.

A C4 record over the same old input and label group has an actual IndActionData
C4.ind.  If its place v is equal to oldPlaceData D.v, the carrier types agree and
C4.ind transports by definitional equality of ThetaPilotPoint along that v
equality.  No arbitrary transport map is introduced.

No C4 record over the old input, and no place equality, is provided by
P6BridgeDonors.  That is the exact named gap.  The old carrier also has no
C4.ind of its own.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C4OldCarrierIndActionAttempt

open LeanFormal.IUT
open LeanFormal.IUT.ConcreteFiniteTheorem311
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
open LeanFormal.IUT.N8Closure.C4IndActionDataActualAttempt
open ABCBridge.N8.C4Actual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- C4 data over the old bridge input and the canonical finite-label group. -/
abbrev OldCarrierC4Data (D : P6BridgeDonors X) :=
  SourceWitnessedOutputData (l := l) (V := NativePlaces X.S)
    (actualBridge D).input (Multiplicative (finiteLabel l))

/-- Exact place alignment needed to identify the C4 carrier with the old
carrier. -/
def OldCarrierPlaceAlignment (D : P6BridgeDonors X)
    (C4 : OldCarrierC4Data D) : Prop :=
  C4.place.v = (oldPlaceData D).v

/-- Actual transport of C4.ind to the old carrier along the place equality.
Only definitional dependent transport is used; no arbitrary map. -/
noncomputable def oldIndActionDataOfC4 (D : P6BridgeDonors X)
    (C4 : OldCarrierC4Data D) (h : OldCarrierPlaceAlignment D C4) :
    OldIndActionData D :=
  Eq.ndrec (motive := fun v =>
    IndActionData ((actualBridge D).input.ThetaPilotPoint v)
      (Multiplicative (finiteLabel l))) C4.ind h

/-- Conditional actual old-carrier IndActionData. -/
theorem oldIndActionData_nonempty_of_c4 (D : P6BridgeDonors X)
    (C4 : OldCarrierC4Data D) (h : OldCarrierPlaceAlignment D C4) :
    Nonempty (OldIndActionData D) :=
  ⟨oldIndActionDataOfC4 D C4 h⟩

/-- Exact minimal named gap: an actual C4 over the old input with aligned
place.  No arbitrary C4 or place transport is supplied. -/
def OldCarrierC4AlignmentExists (D : P6BridgeDonors X) : Prop :=
  ∃ C4 : OldCarrierC4Data D, OldCarrierPlaceAlignment D C4

/-- Old-carrier IndActionData via the exact alignment gap. -/
theorem oldIndActionData_nonempty_of_alignment (D : P6BridgeDonors X)
    (h : OldCarrierC4AlignmentExists D) :
    Nonempty (OldIndActionData D) := by
  obtain ⟨C4, hC4⟩ := h
  exact oldIndActionData_nonempty_of_c4 D C4 hC4

end LeanFormal.IUT.N8Closure.C4OldCarrierIndActionAttempt
