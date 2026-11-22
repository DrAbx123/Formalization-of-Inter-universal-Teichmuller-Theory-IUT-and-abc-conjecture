import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2718PlaceVQInterfaceActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{0, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The rational-valuation index of the actual C3 tensor packet. -/
abbrev LiteralVQ : Type := C3.tensorIndex

/-- The places over a VQ-index: the actual tensor place index. -/
abbrev LiteralPlace (vQ : LiteralVQ C3) : Type := C3.tensorPlaceIndex vQ

/-- The actual finite place over `vQ` and `v`. -/
def literalPlace (vQ : LiteralVQ C3) (v : LiteralPlace C3 vQ) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  C3.tensorPlaces vQ v

instance literalPlaceFintype (vQ : LiteralVQ C3) :
    Fintype (LiteralPlace C3 vQ) :=
  C3.tensorFintype vQ

/-- The S_{j+1} x VQ index of the literal IQ carrier. -/
abbrev LiteralIQIndex (j : Nat) : Type := Fin (j + 1) × LiteralVQ C3

/-- The place index of the literal IQ carrier at an IQ index. -/
abbrev LiteralIQPlaceIndex (j : Nat) (x : LiteralIQIndex C3 j) : Type :=
  LiteralPlace C3 x.2

/-- The actual completion-packet place family of the literal IQ carrier. -/
def literalIQPlaces (j : Nat) (x : LiteralIQIndex C3 j)
    (v : LiteralIQPlaceIndex C3 j x) :
    FinitePlaceAtPrime I.initial.arithmetic.Fmod C3.p :=
  literalPlace C3 x.2 v

instance literalIQPlaceFintype (j : Nat) (x : LiteralIQIndex C3 j) :
    Fintype (LiteralIQPlaceIndex C3 j x) :=
  literalPlaceFintype C3 x.2

/-- The place/VQ identification: the literal IQ place at `(i, vQ)` is the
actual tensor place over `vQ`. -/
theorem literalIQPlaces_eq_tensorPlace (j : Nat) (i : Fin (j + 1))
    (vQ : LiteralVQ C3) (v : LiteralPlace C3 vQ) :
    literalIQPlaces C3 j (i, vQ) v = C3.tensorPlaces vQ v := rfl

/-- The IQ index is exactly `S_{j+1} x VQ`. -/
theorem literalIQIndex_eq_prod (j : Nat) :
    LiteralIQIndex C3 j = (Fin (j + 1) × LiteralVQ C3) := rfl

/-- The place index is exactly the place family over the second IQ coordinate. -/
theorem literalIQPlaceIndex_eq (j : Nat) (x : LiteralIQIndex C3 j) :
    LiteralIQPlaceIndex C3 j x = LiteralPlace C3 x.2 := rfl

#check LiteralVQ
#check LiteralPlace
#check literalPlace
#check literalIQPlaces_eq_tensorPlace
#print axioms literalIQPlaces_eq_tensorPlace
end LeanFormal.IUT.XiFPaper.S2718PlaceVQInterfaceActualAdapted
end
