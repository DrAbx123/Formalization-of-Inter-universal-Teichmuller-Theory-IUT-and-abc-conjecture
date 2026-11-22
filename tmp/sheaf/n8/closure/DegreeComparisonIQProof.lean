import tmp.sheaf.n8.closure.SourceDegreeComparisonIQ

set_option maxHeartbeats 400000
set_option relaxedAutoImplicit false

/-!
# C8IQ proof: corrected degree/normalization identity

Stage-3 proof draft for the corrected C8 statement
`iqDegree B = B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog)`.

The arbitrary-B equality is not derivable from the stage-2 interface (the
fields are independent).  The provable statement is the actual-data instance
`B = C6ActualIQData.actual`; it is definitional from the C6 donors.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.C8IQ

namespace LeanFormal.IUT.N8Closure.C8IQProof

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
  {I : OriginalInput l V}
  {LAdd : Type uG} [AddGroup LAdd]

variable (C1 : SourceInputBinding I)
  (C2 : SourceLogKummerData I C1)
  (C3 : SourcePilotRegionData (l := l) (V := V) I)
  (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
  (C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 D)
  [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
  [Measure.IsAddHaarMeasure mu]
  (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu)

/-- Exact C6 normalization identity for the actual C6 IQ data. -/
theorem iqDegree_eq_normalization_of_actual
    (hB : B = C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) :
    iqDegree (C3 := C3) (mu := mu) B =
      B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog) := by
  subst hB
  rfl

/-- The same identity stated directly for `C6ActualIQData.actual`. -/
theorem iqDegree_actual_eq_normalization :
    iqDegree (C3 := C3) (mu := mu)
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).normalizationWeight *
        ((C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).signedHullLog -
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).unitReferenceLog) := by
  rfl

end LeanFormal.IUT.N8Closure.C8IQProof

end