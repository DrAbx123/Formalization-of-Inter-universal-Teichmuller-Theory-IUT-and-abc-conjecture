import tmp.sheaf.xif.paper.PrimeStripLogShellActual
import tmp.sheaf.xif.paper.GlobalThetaPilotIQEmbeddingActualAdapted

/-!
# Global Theta-pilot IQ embedding from prime-strip place comparison

PrimeStripLogShellActual supplies the actual D/F prime-strip capsule and the
exact missing comparison

  PrimeStripC3PlaceComparison :
    V ~= C3.tensorIndex and stripPlace v = C3.tensorPlaces (indexEquiv v) ...

This file uses that comparison to construct the actual index alignment between
the literal IQ index Fin (j+1) x C3.tensorIndex and the source index
Fin (j+1) x V, and proves the place agreement for literalIQPlaces.

The remaining datum for an actual GlobalThetaPilotIQEmbedding is a value-level
transport from the global product ThetaPilotPoint carrier into the literal IQ
tensor packet.  No such map is supplied by the prime-strip place comparison; it
is recorded as the exact embedding obstruction, not fabricated.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQEmbeddingFromPrimeStripActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.XiFPaper.GlobalIQHullThetaPilotActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQEmbeddingActualAdapted

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [forall i, Fintype (C3.tensorPlaceIndex i)]
variable (j : Nat)
variable (P : PrimeStripC3PlaceComparison (V := V) (I := I) C3)

/-- The source index Fin (j+1) x V is equivalent to the literal IQ index
Fin (j+1) x C3.tensorIndex under the actual place comparison. -/
def sourceToLiteralIQIndex :
    (Fin (j + 1) × V) ≃ LiteralIQIndex (C3 := C3) j :=
  Equiv.prodCongr (Equiv.refl (Fin (j + 1))) P.indexEquiv

/-- The literal IQ places at the aligned index are the selected C3 tensor
places from the prime-strip comparison. -/
theorem literalIQPlaces_source_eq
    (x : Fin (j + 1) × V) :
    literalIQPlaces (C3 := C3) j (sourceToLiteralIQIndex (C3 := C3) j P x) =
      C3.tensorPlaces (P.indexEquiv x.2)
        (C3.tensorTuple (P.indexEquiv x.2)) := by
  rfl

/-- The prime-strip place at x.2 is the selected C3 tensor place. -/
theorem stripPlace_eq_c3TensorPlace (x : Fin (j + 1) × V) :
    P.stripPlace x.2 =
      C3.tensorPlaces (P.indexEquiv x.2)
        (C3.tensorTuple (P.indexEquiv x.2)) :=
  P.stripPlace_eq x.2

/-- Exact value-level transport datum still required for the global embedding:
a map from the global product ThetaPilotPoint carrier into the literal IQ
ambient, compatible with the place alignment. -/
structure GlobalThetaPilotIQValueTransport where
  embed : GlobalThetaPilotCarrier (I := I) → LiteralIQAmbient (C3 := C3) j

/-- The exact embedding obstruction after the place comparison: the
prime-strip place alignment exists only conditionally, and no value transport is
supplied by the actual D/F comparison. -/
def GlobalThetaPilotIQEmbeddingFromPrimeStripObstruction : Prop :=
  Nonempty (PrimeStripC3PlaceComparison (V := V) (I := I) C3) ∧
    Nonempty (GlobalThetaPilotIQValueTransport (I := I) C3 j)

/-- If the value transport is supplied, the actual GlobalThetaPilotIQEmbeddingData
is constructed. -/
noncomputable def globalThetaPilotIQEmbeddingOfPrimeStrip
    (T : GlobalThetaPilotIQValueTransport (I := I) C3 j) :
    GlobalThetaPilotIQEmbeddingData (I := I) C3 j where
  embed := T.embed

/-- The constructed embedding's map is the supplied value transport. -/
theorem globalThetaPilotIQEmbeddingOfPrimeStrip_embed
    (T : GlobalThetaPilotIQValueTransport (I := I) C3 j) :
    (globalThetaPilotIQEmbeddingOfPrimeStrip (I := I) C3 j T).embed =
      T.embed := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQEmbeddingFromPrimeStripActualAdapted

end
