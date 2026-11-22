import tmp.sheaf.n8.closure.SourceDegreeActualDegreeBridge

/-! # SourceDegree residual vs the C8 normalized hull volume

After rewriting `SourceDegreeComparisonResidual` to the actual arithmetic degree, the residual is equivalent to the C8 normalized hull-volume equality of the actual `B`, conditional on identifying the C7 hull readout `c8HullLogVolume` with `B.normalizedLogVolume B.hull`. This is exactly the remaining source hull-readout identification; it does not identify the generic C6 carrier with the C3-block `B`.
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

/-- Exact remaining hull-readout identification: the C7 C8 hull log-volume agrees with the actual C8 normalized hull volume of `B`. -/
def SourceDegreeHullReadoutIdentification
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n) : Prop :=
  c8HullLogVolume (V := V) (places := places) (tuple := tuple)
    C6 C6Prod C7 = B.normalizedLogVolume B.hull

/-- The SourceDegree residual is equivalent to the actual arithmetic degree equalling `B.normalizedLogVolume B.hull`, given the C7 hull readout identification. -/
theorem sourceDegreeResidual_iff_actualDegree_eq_BHull
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n)
    (hHull : c8HullLogVolume (V := V) (places := places) (tuple := tuple)
      C6 C6Prod C7 = B.normalizedLogVolume B.hull) :
    SourceDegreeComparisonResidual (V := V) (places := places)
      (tuple := tuple) C6 C6Prod C7 ↔
      actualArithmeticDegree C6 = B.normalizedLogVolume B.hull := by
  rw [sourceDegreeResidual_iff_actualArithmeticDegree, hHull]

/-- Conditional form through the named hull-readout identification. -/
theorem sourceDegreeResidual_iff_actualDegree_eq_BHull_of_readout
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n)
    (h : SourceDegreeHullReadoutIdentification (V := V) (places := places)
      (tuple := tuple) C6 C6Prod C7) :
    SourceDegreeComparisonResidual (V := V) (places := places)
      (tuple := tuple) C6 C6Prod C7 ↔
      actualArithmeticDegree C6 = B.normalizedLogVolume B.hull :=
  sourceDegreeResidual_iff_actualDegree_eq_BHull C6 C6Prod C7 h

end LeanFormal.IUT.N8Closure.C8
end