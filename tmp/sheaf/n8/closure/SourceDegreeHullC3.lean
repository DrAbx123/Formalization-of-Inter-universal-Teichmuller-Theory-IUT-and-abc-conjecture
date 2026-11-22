import tmp.sheaf.n8.closure.SourceDegreeHullComponents

/-! # Hull-readout identity on the C3 tensor block

This instantiates the generic component theorem on the C3 tensor block, where all three components should be definitional.

Conditional interface: C6/C6Prod/C7 are variables; no actual PaperNormalizedVolumeData/C6ProductVolumeData instance is constructed here.
-/

noncomputable section
set_option maxHeartbeats 4000000
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

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V0 : Type uv} {Label : Type uL} [Group Label]
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V0}
  {D : SourceWitnessedOutputData (l := l) (V := V0) I Label}
  {C5 : C5PermittedFamilyData (l := l)}
  {C1 : SourceInputBinding I}
  {C2 : SourceLogKummerData I C1}
  (C3 : SourcePilotRegionData (l := l) (V := V0) I)
  [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  {LAdd : Type uG} [AddGroup LAdd]
  {Dalg : SourceWitnessedOutputData (l := l) (V := V0) I (Multiplicative LAdd)}
  {C5Alg : SourceAlgorithmCompatibilityData I C1 C2 C3 Dalg}
  {muIQ : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
  [Measure.IsAddHaarMeasure muIQ]
  {T : SourceThetaIQInterface (I := I) C3}
  {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}
  {C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v)}

theorem c8HullLogVolume_c3_eq_normalizedLogVolume
    (C6 : PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n) :
    c8HullLogVolume (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        C6 C6Prod C7 =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull := by
  exact c8HullLogVolume_actual_eq_normalizedLogVolume
    (K := I.initial.arithmetic.Fmod) (p := C3.p)
    (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple)
    (mu := muIQ) C6 C6Prod C7 rfl rfl rfl

/-- On the C3 tensor block the named hull-readout identification holds unconditionally. -/
theorem sourceDegreeHullReadoutIdentification_c3
    (C6 : PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n) :
    SourceDegreeHullReadoutIdentification
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) C6 C6Prod C7 :=
  c8HullLogVolume_c3_eq_normalizedLogVolume C3 C6 C7

/-- End-to-end SourceDegree residual form for C6 on the actual C3 tensor block, unconditionally. -/
theorem sourceDegreeResidual_iff_actualDegree_eq_BHull_c3
    (C6 : PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n) :
    SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      C6 C6Prod C7 ↔
      actualArithmeticDegree
        (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        C6 =
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  sourceDegreeResidual_iff_actualDegree_eq_BHull_of_readout
    (K := I.initial.arithmetic.Fmod) (p := C3.p)
    (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
    (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ)
    C6 C6Prod C7 (sourceDegreeHullReadoutIdentification_c3 C3 C6 C7)

end LeanFormal.IUT.N8Closure.C8
end