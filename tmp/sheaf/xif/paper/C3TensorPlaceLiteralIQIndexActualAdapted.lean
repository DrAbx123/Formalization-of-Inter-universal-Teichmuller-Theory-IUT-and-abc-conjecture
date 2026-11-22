import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual
import tmp.sheaf.xif.paper.GlobalThetaPilotKummerActualAdapted

/-!
# Actual C3 tensor-place / LiteralIQ place comparison

IUT III, Proposition 3.2 and the tensor-packet construction: the literal IQ
ambient of a tensor packet is indexed by

  LiteralIQIndex j = Fin (j+1) x C3.tensorIndex,
  LiteralIQPlaceIndex (t,i) = C3.tensorPlaceIndex i,
  literalIQPlaces (t,i) = C3.tensorPlaces i.

This file constructs the actual index equivalence and place comparison by
definition, and the actual place equality for every literal-IQ index.  It also
records the exact missing datum for inserting the q-generated completion image
into the ambient: a C3 tensor index (i,a) whose actual place C3.tensorPlaces i a
is C3.place.  Without that place identification no actual tensor embedding of
the completion image is asserted.

No arbitrary equivalence or fake embedding.  No empty type, no True/PUnit,
axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.C3TensorPlaceLiteralIQIndexActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotKummerActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual index equivalence between the literal IQ index and
Fin(j+1) x C3.tensorIndex. -/
def literalIQIndexEquiv (j : Nat) :
    LiteralIQIndex (C3 := C3) j ≃ Fin (j + 1) × C3.tensorIndex :=
  Equiv.refl _

/-- The actual place-index equality at every literal IQ index. -/
theorem literalIQPlaceIndex_eq
    (j : Nat) (x : LiteralIQIndex (C3 := C3) j) :
    LiteralIQPlaceIndex (C3 := C3) j x = C3.tensorPlaceIndex x.2 := rfl

/-- The actual place equality at every literal IQ place index. -/
theorem literalIQPlaces_eq
    (j : Nat) (x : LiteralIQIndex (C3 := C3) j)
    (a : LiteralIQPlaceIndex (C3 := C3) j x) :
    literalIQPlaces (C3 := C3) j x a = C3.tensorPlaces x.2 a := rfl

/-- The actual C3 tensor place at zero procession index. -/
theorem literalIQPlaces_at_zero
    (j : Nat) (i : C3.tensorIndex) (a : C3.tensorPlaceIndex i) :
    literalIQPlaces (C3 := C3) j
        (⟨0, Nat.succ_pos j⟩, i) a = C3.tensorPlaces i a := rfl

/-- The actual index/place comparison data. -/
structure C3TensorPlaceLiteralIQComparison (j : Nat) where
  indexEquiv : LiteralIQIndex (C3 := C3) j ≃ Fin (j + 1) × C3.tensorIndex
  placeIndex_eq : ∀ x : LiteralIQIndex (C3 := C3) j,
    LiteralIQPlaceIndex (C3 := C3) j x = C3.tensorPlaceIndex x.2
  place_eq : ∀ (x : LiteralIQIndex (C3 := C3) j)
      (a : LiteralIQPlaceIndex (C3 := C3) j x),
    literalIQPlaces (C3 := C3) j x a = C3.tensorPlaces x.2 a

/-- The actual comparison at every procession level. -/
noncomputable def c3TensorPlaceLiteralIQComparison (j : Nat) :
    C3TensorPlaceLiteralIQComparison (I := I) (C3 := C3) j where
  indexEquiv := literalIQIndexEquiv (C3 := C3) j
  placeIndex_eq := literalIQPlaceIndex_eq (C3 := C3) j
  place_eq := literalIQPlaces_eq (C3 := C3) j

/-- Exact source datum needed to insert the completion image at C3.place into
the literal IQ ambient: a C3 tensor place equal to C3.place. -/
structure C3PlaceTensorWitness where
  i : C3.tensorIndex
  a : C3.tensorPlaceIndex i
  place_eq : C3.tensorPlaces i a = C3.place

/-- The exact missing place-identification target. -/
def C3PlaceTensorWitnessTarget : Prop :=
  Nonempty (C3PlaceTensorWitness (C3 := C3))

/-- The comparison identifies the literal IQ place family with the C3 tensor
place family at every index; the insertion witness is separate. -/
theorem c3TensorPlaceLiteralIQComparison_status
    (j : Nat) :
    Nonempty (C3TensorPlaceLiteralIQComparison (C3 := C3) j) ∧
      (C3PlaceTensorWitnessTarget (C3 := C3) ↔
        Nonempty (C3PlaceTensorWitness (C3 := C3))) :=
  ⟨⟨c3TensorPlaceLiteralIQComparison (C3 := C3) j⟩, Iff.rfl⟩

end LeanFormal.IUT.XiFPaper.C3TensorPlaceLiteralIQIndexActualAdapted
