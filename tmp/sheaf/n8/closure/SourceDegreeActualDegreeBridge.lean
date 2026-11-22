import tmp.sheaf.n8.closure.SourceDegreeComparison
import tmp.sheaf.n8.closure.C8DegreeActual

/-! # SourceDegree residual in terms of the actual arithmetic degree

`SourceDegreeComparisonResidual` is the equality of `c8RelativeDetDegree` with the C7 hull log-volume. Since `c8RelativeDetDegree` is definitionally the C8 actual arithmetic degree, the residual is equivalently the equality of `actualArithmeticDegree` with the same hull log-volume. This is the exact scalar form of the remaining (Ob3-3) comparison.
-/

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.C8
open LeanFormal.IUT.N8Closure.C8DegreeActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open ABCBridge.N8.C7Actual
open ABCBridge.N8.C4Actual

namespace LeanFormal.IUT.N8Closure.C8

universe ua uv upi umon ui uL uY uK uG u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  {iota : Type v} [Fintype iota] {V : iota → Type w}
  {places : (i : iota) → V i → FinitePlaceAtPrime K p}
  {tuple : (i : iota) → V i}
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
  [Measure.IsAddHaarMeasure mu]

variable {l : PrimeGeFive} {V0 : Type uv} {Label : Type uL} [Group Label]
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V0}
  {D : SourceWitnessedOutputData (l := l) (V := V0) I Label}
  {C5 : C5PermittedFamilyData (l := l)}
  {C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v)}
  {C1 : SourceInputBinding I}
  {C2 : SourceLogKummerData I C1}
  {C3 : SourcePilotRegionData (l := l) (V := V0) I}
  [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  {LAdd : Type uG} [AddGroup LAdd]
  {Dalg : SourceWitnessedOutputData (l := l) (V := V0) I (Multiplicative LAdd)}
  {C5Alg : SourceAlgorithmCompatibilityData I C1 C2 C3 Dalg}
  {muIQ : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
  [Measure.IsAddHaarMeasure muIQ]
  {B : C6ActualIQData C3.tensorPlaces C3.tensorTuple muIQ}
  {T : SourceThetaIQInterface (I := I) C3}
  {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}

/-- The SourceDegree residual is exactly the scalar equality of the actual arithmetic degree with the C7 hull log-volume. -/
theorem sourceDegreeResidual_iff_actualArithmeticDegree
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n) :
    SourceDegreeComparisonResidual (V := V) (places := places)
      (tuple := tuple) C6 C6Prod C7 ↔
      actualArithmeticDegree C6 =
        c8HullLogVolume (V := V) (places := places) (tuple := tuple)
          C6 C6Prod C7 := by
  unfold SourceDegreeComparisonResidual
  rw [c8RelativeDetDegree_eq_actualArithmeticDegree]

end LeanFormal.IUT.N8Closure.C8
end