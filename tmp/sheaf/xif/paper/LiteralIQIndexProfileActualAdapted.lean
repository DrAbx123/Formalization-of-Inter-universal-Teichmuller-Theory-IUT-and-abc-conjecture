import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Literal IQ index profile: actual C3 tensor index inclusion

Q3 of the intermediate queue needs a ThetaPilotPoint / possible-image map into
LiteralIQAmbient. That map depends on Q1 (valueMonoid -> completion) and Q2
(prime-strip index/place comparison). Before those are available, this file
constructs the actual index-level intermediate map that is available from the
literal IQ carrier itself:

* the actual inclusion of the C3 tensor index into the literal IQ index at
  level j, via the first S_{j+1} factor;
* the actual projection of the literal IQ index back to the C3 tensor index;
* the actual projection to the S_{j+1} factor;
* the pointwise actual place equality showing that the literal IQ places at
  the embedded C3 index are exactly the C3 tensor places;
* the actual embedding/projection round trip.

These are actual definitions and proofs on the literal IQ carrier. No
valueMonoid -> completion map and no prime-strip comparison are fabricated.
No True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.LiteralIQIndexProfileActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]

/-- The actual C3 tensor index as a literal IQ index at level j, placed in the
first S_{j+1} factor. -/
def c3ToLiteralIQIndex (j : Nat) (i : C3.tensorIndex) :
    LiteralIQIndex (C3 := C3) j :=
  (⟨0, Nat.succ_pos j⟩, i)

/-- The actual projection of a literal IQ index to the C3 tensor index. -/
def literalIQIndexToC3 (j : Nat) :
    LiteralIQIndex (C3 := C3) j -> C3.tensorIndex :=
  Prod.snd

/-- The actual projection of a literal IQ index to its S_{j+1} factor. -/
def literalIQIndexToStage (j : Nat) :
    LiteralIQIndex (C3 := C3) j -> Fin (j + 1) :=
  Prod.fst

/-- The projection after the actual C3 index embedding is the identity. -/
theorem literalIQIndexToC3_c3ToLiteralIQIndex (j : Nat)
    (i : C3.tensorIndex) :
    literalIQIndexToC3 (C3 := C3) j (c3ToLiteralIQIndex (C3 := C3) j i) = i :=
  rfl

/-- The stage of an embedded C3 tensor index is zero. -/
theorem literalIQIndexToStage_c3ToLiteralIQIndex (j : Nat)
    (i : C3.tensorIndex) :
    literalIQIndexToStage (C3 := C3) j (c3ToLiteralIQIndex (C3 := C3) j i) =
      (⟨0, Nat.succ_pos j⟩ : Fin (j + 1)) :=
  rfl

/-- The actual place-index type of the literal IQ carrier at an embedded C3
tensor index is the C3 tensor place-index type. -/
theorem literalIQPlaceIndex_c3ToLiteralIQIndex (j : Nat)
    (i : C3.tensorIndex) :
    LiteralIQPlaceIndex (C3 := C3) j
      (c3ToLiteralIQIndex (C3 := C3) j i) =
      C3.tensorPlaceIndex i :=
  rfl

/-- The actual literal IQ places at an embedded C3 tensor index are exactly the
C3 tensor places. -/
theorem literalIQPlaces_c3ToLiteralIQIndex (j : Nat)
    (i : C3.tensorIndex) :
    literalIQPlaces (C3 := C3) j
      (c3ToLiteralIQIndex (C3 := C3) j i) =
      C3.tensorPlaces i :=
  rfl

/-- The actual index-level comparison data: C3 tensor index, stage projection,
C3 projection, and pointwise place equality. -/
structure LiteralIQIndexProfile (j : Nat) where
  toLiteral : C3.tensorIndex -> LiteralIQIndex (C3 := C3) j
  toC3 : LiteralIQIndex (C3 := C3) j -> C3.tensorIndex
  toStage : LiteralIQIndex (C3 := C3) j -> Fin (j + 1)
  toC3_toLiteral : forall i, toC3 (toLiteral i) = i
  place_eq : forall i, literalIQPlaces (C3 := C3) j (toLiteral i) =
    C3.tensorPlaces i

/-- The actual index profile from the literal IQ carrier construction. -/
def literalIQIndexProfile (j : Nat) :
    LiteralIQIndexProfile (C3 := C3) j where
  toLiteral := c3ToLiteralIQIndex (C3 := C3) j
  toC3 := literalIQIndexToC3 (C3 := C3) j
  toStage := literalIQIndexToStage (C3 := C3) j
  toC3_toLiteral := fun i =>
    literalIQIndexToC3_c3ToLiteralIQIndex (C3 := C3) j i
  place_eq := fun i =>
    literalIQPlaces_c3ToLiteralIQIndex (C3 := C3) j i

end LeanFormal.IUT.XiFPaper.LiteralIQIndexProfileActualAdapted

end
