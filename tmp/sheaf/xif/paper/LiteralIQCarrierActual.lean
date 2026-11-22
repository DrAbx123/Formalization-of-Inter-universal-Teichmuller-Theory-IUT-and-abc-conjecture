import tmp.sheaf.xif.paper.IQCarrierObligationsActual
import tmp.sheaf.xif.paper.IQCarrierFromSource

/-! # CONDITIONAL STATUS (xi-f)

Conditional: image_hull_realization is proved, but the literal IQ carrier type/identification (literal_IQ_carrier) is missing. C6 carrier is not claimed to be the literal paper carrier.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Literal IQ carrier actual: image/hull realization and exact missing label

Task-581 write-only construction.  From the actual C7
`SourceHolomorphicHullObligations` we derive the `image_hull_realization`
field (source theta image contained in the actual C6 canonical hull) and build
the actual IQ interface on the C6 tensor carrier.  The only non-constructed
field is `literal_IQ_carrier`: there is no literal
`IQ(S+_{j+1}; n,circ D^vdash_{vQ})` type in the tree, so its identification is
an explicit proposition, not a toy object.

## Constructed

* `imageHullRealization_of_obligations`: actual source theta image containment
  in `(C6ActualIQData.actual ...).hull`.
* `LiteralIQCarrierActual`: actual `IQHullLogVolumeInterface` over the C6 IQ
  carrier plus the proved image containment and the explicit literal label
  proposition.
* `literalIQCarrierActualOfObligations`: constructor from the C7 obligations
  and an explicit literal-label proposition.
* Projection theorems for image set, hull, containment, and interface fields.

No PUnit, True, sorry, axiom, or fake literal carrier is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.N8Closure.PaperIQCarrierActual
namespace Literal

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)

/-- Actual image/hull realization derived from the C7 hull obligations. -/
theorem imageHullRealization_of_obligations
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n) :
    SourceThetaToIQ.image (I := I) C3 T n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull :=
  image_subset_c6Hull_of_obligations C3 mu T n O

/-- The actual IQ-carrier surface with the image/hull realization proved and
the literal label left explicit. -/
structure LiteralIQCarrierActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l)
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    [Measure.IsAddHaarMeasure mu] where
  /-- Actual IQ hull/log-volume interface over the C6 IQ carrier. -/
  interface : IQHullLogVolumeInterface
    (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)
  /-- The interface image set is the actual source theta image. -/
  interface_imageSet_eq :
    interface.imageSet = SourceThetaToIQ.image (I := I) C3 T n
  /-- The interface hull is the actual C6 canonical hull. -/
  interface_hull_eq :
    interface.hull = (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull
  /-- Actual source image containment in the interface hull. -/
  image_hull_realization :
    SourceThetaToIQ.image (I := I) C3 T n ⊆ interface.hull
  /-- Exact missing literal label: the C6 tensor block is the literal
  `IQ(S+_{j+1}; n,circ D^vdash_{vQ})` carrier.  No such type exists in the
  tree; this is a proposition, not an asserted identification. -/
  literal_IQ_carrier : Prop

namespace LiteralIQCarrierActual

variable {C3 : SourcePilotRegionData (l := l) (V := V) I}
variable {T : SourceThetaIQInterface (I := I) C3}
variable {n : ThetaPilotCarrier l}
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable {mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
variable [Measure.IsAddHaarMeasure mu]

theorem imageSet_eq_source (A : LiteralIQCarrierActual C3 T n mu) :
    A.interface.imageSet = SourceThetaToIQ.image (I := I) C3 T n :=
  A.interface_imageSet_eq

theorem hull_eq_c6 (A : LiteralIQCarrierActual C3 T n mu) :
    A.interface.hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull :=
  A.interface_hull_eq

theorem image_subset_hull (A : LiteralIQCarrierActual C3 T n mu) :
    A.interface.imageSet ⊆ A.interface.hull :=
  A.interface.imageSet_subset_hull

theorem image_hull_realization_spec (A : LiteralIQCarrierActual C3 T n mu) :
    SourceThetaToIQ.image (I := I) C3 T n ⊆ A.interface.hull :=
  A.image_hull_realization

theorem hull_logVolume_lt_top (A : LiteralIQCarrierActual C3 T n mu) :
    A.interface.logVolume A.interface.hull < ⊤ :=
  IQHullLogVolumeInterface.hull_logVolume_lt_top A.interface

theorem imageSet_logVolume_le_hull (A : LiteralIQCarrierActual C3 T n mu) :
    A.interface.logVolume A.interface.imageSet ≤
      A.interface.logVolume A.interface.hull :=
  IQHullLogVolumeInterface.imageSet_logVolume_le_hull A.interface

end LiteralIQCarrierActual

/-- Construct the literal IQ carrier surface from the C7 obligations and an
explicit literal-label proposition. -/
def literalIQCarrierActualOfObligations
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n)
    (literal_IQ_carrier : Prop) :
    LiteralIQCarrierActual C3 T n mu where
  interface := actualIQInterface C3 T n mu
    (imageHullRealization_of_obligations C3 mu T n O)
  interface_imageSet_eq := rfl
  interface_hull_eq := rfl
  image_hull_realization :=
    imageHullRealization_of_obligations C3 mu T n O
  literal_IQ_carrier := literal_IQ_carrier

@[simp] theorem literalIQCarrierActualOfObligations_interface
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n)
    (literal_IQ_carrier : Prop) :
    (literalIQCarrierActualOfObligations C3 mu T n O literal_IQ_carrier).interface =
      actualIQInterface C3 T n mu
        (imageHullRealization_of_obligations C3 mu T n O) := rfl

@[simp] theorem literalIQCarrierActualOfObligations_imageSet
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n)
    (literal_IQ_carrier : Prop) :
    (literalIQCarrierActualOfObligations C3 mu T n O literal_IQ_carrier).interface.imageSet =
      SourceThetaToIQ.image (I := I) C3 T n := rfl

@[simp] theorem literalIQCarrierActualOfObligations_hull
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n)
    (literal_IQ_carrier : Prop) :
    (literalIQCarrierActualOfObligations C3 mu T n O literal_IQ_carrier).interface.hull =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull := rfl

end Literal
end LeanFormal.IUT.N8Closure.PaperIQCarrierActual

end
