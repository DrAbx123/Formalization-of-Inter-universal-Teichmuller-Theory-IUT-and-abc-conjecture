import tmp.sheaf.n8.closure.SourceDegreeHullBridge

/-! # Component form of the hull-readout identification

For the actual C8 IQ data, `c8HullLogVolume` agrees with the actual normalized log-volume of the canonical hull once the C6 local-volume degree and unit-reference log match the actual arithmetic normalization. This isolates the remaining source data as two scalar equalities plus the common-hull identification.
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
  {T : SourceThetaIQInterface (I := I) C3}
  {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}

/-- For the actual IQ data, the C7 hull readout equals the actual normalized canonical-hull volume once the C6 local-volume degree and unit-reference log match. -/
theorem c8HullLogVolume_actual_eq_normalizedLogVolume
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n)
    (hunitRef : mu (arithmeticTupleCanonicalUnitReference places tuple) =
      muIQ (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple))
    (hp : p = C3.p)
    (hfr : (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) =
      (Module.finrank ℚ_[C3.p] (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) : ℝ)) :
    c8HullLogVolume (V := V) (places := places) (tuple := tuple) C6 C6Prod C7 =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull := by
  unfold c8HullLogVolume
  simp only [C6ActualIQData.actual, commonHull, arithmeticTupleNormalizedLogVolume,
    arithmeticTupleCanonicalHull]
  subst p
  have hunit : C6.localVolume.unitReferenceLog =
      Real.log (muIQ (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple)).toReal := by
    rw [C6.localVolume.unitReferenceLog_eq, hunitRef]
  rw [C6.localVolume.degree_eq, hunit, hfr]

/-- The named hull-readout identification holds for the actual IQ data under the three source components. -/
theorem sourceDegreeHullReadoutIdentification_actual
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n)
    (hunitRef : mu (arithmeticTupleCanonicalUnitReference places tuple) =
      muIQ (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple))
    (hp : p = C3.p)
    (hfr : (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) =
      (Module.finrank ℚ_[C3.p] (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) : ℝ)) :
    SourceDegreeHullReadoutIdentification (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ)
      (V := V) (places := places) (tuple := tuple) C6 C6Prod C7 :=
  c8HullLogVolume_actual_eq_normalizedLogVolume (V := V) (places := places)
    (tuple := tuple) C6 C6Prod C7 hunitRef hp hfr

/-- End-to-end SourceDegree residual form for the actual C8 IQ data. -/
theorem sourceDegreeResidual_iff_actualDegree_eq_BHull_actual
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n)
    (hunitRef : mu (arithmeticTupleCanonicalUnitReference places tuple) =
      muIQ (arithmeticTupleCanonicalUnitReference C3.tensorPlaces C3.tensorTuple))
    (hp : p = C3.p)
    (hfr : (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ) =
      (Module.finrank ℚ_[C3.p] (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) : ℝ)) :
    SourceDegreeComparisonResidual (V := V) (places := places) (tuple := tuple)
      C6 C6Prod C7 ↔
      actualArithmeticDegree C6 =
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  sourceDegreeResidual_iff_actualDegree_eq_BHull_of_readout
    (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ)
    (V := V) (places := places) (tuple := tuple) C6 C6Prod C7
    (sourceDegreeHullReadoutIdentification_actual C6 C6Prod C7 hunitRef hp hfr)

end LeanFormal.IUT.N8Closure.C8
end