import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.xif.paper.PaperIQCarrierActual

/-! # Actual IQ-carrier image containment from C7 obligations

The C7 source-hull obligations contain the actual theta-image containment in
the common hull. At the actual C6 hull this is exactly the hImage donor of
PaperIQCarrierActual.actualIQInterface. This file derives it and packages the
paper IQ-carrier record, leaving the literal O-module/compactness and
normalization fields as exact obligations.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.N8Closure.PaperIQCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
open ABCBridge.N8.C7Actual
open MeasureTheory

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)

/-- The actual theta image is contained in the actual C6 canonical hull. -/
theorem image_subset_c6Hull_of_obligations
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n) :
    SourceThetaToIQ.image (I := I) C3 T n ⊆
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).hull := by
  simpa [permittedImage, commonHull] using O.image_subset_hull

/-- The paper IQ-carrier record from the C7 obligations and the exact literal
IQ/O-module/compactness obligations. -/
def paperIQCarrierActualOfObligations
    (O : SourceHolomorphicHullObligations C3 mu
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) T n)
    (missing : PaperIQCarrierMissingFields) :
    PaperIQCarrierActual (I := I) C3 T n mu where
  interface := actualIQInterface C3 T n mu
    (image_subset_c6Hull_of_obligations C3 mu T n O)
  interface_imageSet_eq := rfl
  interface_hull_eq := rfl
  missing := missing

end LeanFormal.IUT.N8Closure.PaperIQCarrierActual
end