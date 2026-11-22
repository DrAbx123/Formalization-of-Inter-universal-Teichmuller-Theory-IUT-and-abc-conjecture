import tmp.sheaf.n8.closure.C1ActualInputQuotientConsumer
import tmp.sheaf.n8.closure.P6Bridge
import tmp.sheaf.n8.closure.PaperN8Closure

/-!
# C1NativeConsumerPaperRoute

Defines the paper-route C1 layer over the native/actual source input:
`NativeC1PaperRoute X` packages `NativeC1QuotientConsumer X` (actual native C1
place/selected data plus corrected quotient fiber data).  It is constructed
without arbitrary old `OriginalInput`.

Consumer status:

- CAN switch to this C1 layer: native C1 quotient consumers and future native
  C2/C3/C7 slices that need native places/selected data plus quotient fibers.
- CANNOT switch without an adapter:
  * `P6BridgeDonors`/`NativeOldC1Bridge` still require a `SourceDefinition31Data`
    contract datum and old `SourceImageRealization`/fiber donors; they are not
    supplied by the native C1 consumer.
  * `PaperN8Output`/`N8RouteObligations` have P6 Chain A/B, hull, readout and
    comparison fields and no C1 slot; they cannot consume this interface
    without a new explicit adapter declaration.  This is a target correction,
    not an actual connection.

No total-goal sorry; interface itself is actual.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C1ActualInputQuotientConsumer

variable {l : PrimeGeFive}

/-- Paper-route C1 layer over native input: the actual native quotient
consumer, no old `OriginalInput`. -/
structure NativeC1PaperRoute (X : N8NativeInput l) where
  /-- Actual native C1 quotient consumer. -/
  c1 : NativeC1QuotientConsumer X

/-- Actual paper-route C1 interface from the native consumer. -/
noncomputable def nativeC1PaperRoute (X : N8NativeInput l) :
    NativeC1PaperRoute X where
  c1 := nativeC1QuotientConsumer X

/-- The paper-route C1 layer is actually inhabited for every native input. -/
theorem nativeC1PaperRoute_nonempty (X : N8NativeInput l) :
    Nonempty (NativeC1PaperRoute X) :=
  ⟨nativeC1PaperRoute X⟩

/-- Exact distinction: the native paper-route C1 layer does not provide the
old contract donor needed by P6Bridge. -/
abbrev P6BridgeStillNeedsOldContract (X : N8NativeInput l) : Prop :=
  LeanFormal.IUT.N8Closure.P6Bridge.P6BridgeDonorsExist X

end LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute