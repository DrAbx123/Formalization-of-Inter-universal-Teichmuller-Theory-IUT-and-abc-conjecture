import tmp.sheaf.n8.closure.SourceDegreeHullC3
import tmp.sheaf.n8.closure.PaperNormalizedVolumeActualAttempt
import tmp.sheaf.n8.closure.C7ActualFromSource

/-!
# SourceDegree C3 with concrete C6 from paper source data

This file assembles the concrete C6 normalized-volume term from the actual
paper local-volume component and the explicit paper source fields:

  PaperNormalizationSourceData.toPaperNormalizedVolumeData

on the C3 tensor block. It then specializes the C3 hull-readout identification
and the C3 SourceDegree residual pair of SourceDegreeHullC3.lean to this
concrete C6.

C6Prod and C7 remain the exact remaining source fields. The source-data fields
of PaperNormalizationSourceData (lambda weights, tuple weights, procession
length/weights/average, global volume, global normalization identity) are also
still supplied data, not constructed here. No arbitrary constants, wrappers,
axioms, or unfilled proofs are used.
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

/-- The concrete C6 normalized-volume term assembled from the actual paper
local volume and the explicit paper source fields on the C3 tensor block. -/
noncomputable def sourcePaperNormalizedVolumeData
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ) :
    PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple muIQ :=
  S.toPaperNormalizedVolumeData

/-- The local volume of the concrete C6 term is the actual paper local volume. -/
theorem sourcePaperNormalizedVolumeData_localVolume
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ) :
    (sourcePaperNormalizedVolumeData C3 S).localVolume =
      paperLocalVolumeActual C3.tensorPlaces C3.tensorTuple muIQ :=
  rfl

/-- The concrete C6 term carries the supplied lambda data. -/
theorem sourcePaperNormalizedVolumeData_lambdaData
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ) :
    (sourcePaperNormalizedVolumeData C3 S).lambdaData = S.lambdaData :=
  rfl

/-- The concrete C6 term carries the supplied tuple weights. -/
theorem sourcePaperNormalizedVolumeData_tupleWeights
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ) :
    (sourcePaperNormalizedVolumeData C3 S).tupleWeights = S.tupleWeights :=
  rfl

/-- The concrete C6 term carries the supplied procession data. -/
theorem sourcePaperNormalizedVolumeData_procession
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ) :
    (sourcePaperNormalizedVolumeData C3 S).processionLength =
        S.processionLength ∧
      (sourcePaperNormalizedVolumeData C3 S).processionWeights =
        S.processionWeights ∧
      (sourcePaperNormalizedVolumeData C3 S).processionAverageValue =
        S.processionAverageValue :=
  ⟨rfl, rfl, rfl⟩

/-- The concrete C6 term carries the supplied global volume. -/
theorem sourcePaperNormalizedVolumeData_globalVolume
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ) :
    (sourcePaperNormalizedVolumeData C3 S).globalVolume = S.globalVolume :=
  rfl

/-- The C3 hull-readout identity with the concrete C6 term from paper source
data. C6Prod and C7 are the remaining source fields. -/
theorem c8HullLogVolume_c3_eq_normalizedLogVolume_fromSource
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n) :
    c8HullLogVolume (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        (sourcePaperNormalizedVolumeData C3 S) C6Prod C7 =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  c8HullLogVolume_c3_eq_normalizedLogVolume C3
    (sourcePaperNormalizedVolumeData C3 S) C7

/-- The named C3 hull-readout identification with the concrete C6 term from
paper source data. -/
theorem sourceDegreeHullReadoutIdentification_c3_fromSource
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n) :
    SourceDegreeHullReadoutIdentification
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ)
      (sourcePaperNormalizedVolumeData C3 S) C6Prod C7 :=
  sourceDegreeHullReadoutIdentification_c3 C3
    (sourcePaperNormalizedVolumeData C3 S) C7

/-- The C3 SourceDegree residual equivalence with the concrete C6 term from
paper source data. -/
theorem sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSource
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n) :
    SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (sourcePaperNormalizedVolumeData C3 S) C6Prod C7 ↔
      actualArithmeticDegree
        (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        (sourcePaperNormalizedVolumeData C3 S) =
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  sourceDegreeResidual_iff_actualDegree_eq_BHull_c3 C3
    (sourcePaperNormalizedVolumeData C3 S) C7

/-- First direction of the C3 residual pair: the residual follows from the
actual degree-hull equality, with the concrete C6 term. -/
theorem sourceDegreeResidual_of_actualDegree_eq_BHull_c3_fromSource
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n)
    (h : actualArithmeticDegree
        (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        (sourcePaperNormalizedVolumeData C3 S) =
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull) :
    SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (sourcePaperNormalizedVolumeData C3 S) C6Prod C7 :=
  (sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSource C3 S C7).mpr h

/-- Second direction of the C3 residual pair: the actual degree-hull equality
follows from the residual, with the concrete C6 term. -/
theorem actualDegree_eq_BHull_of_sourceDegreeResidual_c3_fromSource
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ)
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ) (T := T) n)
    (h : SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (sourcePaperNormalizedVolumeData C3 S) C6Prod C7) :
    actualArithmeticDegree
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (sourcePaperNormalizedVolumeData C3 S) =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  (sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSource C3 S C7).mp h

/-- C3 residual pair with concrete C6 from paper source fields and concrete C7 hull data: C7 is reduced to the two exact containment obligations. -/
theorem sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSourceHull
    (S : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ)
    (O : LeanFormal.IUT.N8Closure.C7FromSource.C3ConcreteHullObligations
      (C3 := C3) (mu := muIQ) T n) :
    SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      (sourcePaperNormalizedVolumeData C3 S) C6Prod
      (LeanFormal.IUT.N8Closure.C7FromSource.concreteSourceHolomorphicHullData
        (C3 := C3) (mu := muIQ) (C1 := C1) (C2 := C2)
        (D := Dalg) (C5 := C5Alg) (T := T) (n := n) O) ↔
      actualArithmeticDegree
        (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        (sourcePaperNormalizedVolumeData C3 S) =
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSource C3 S
    (LeanFormal.IUT.N8Closure.C7FromSource.concreteSourceHolomorphicHullData
      (C3 := C3) (mu := muIQ) (C1 := C1) (C2 := C2)
      (D := Dalg) (C5 := C5Alg) (T := T) (n := n) O)

end LeanFormal.IUT.N8Closure.C8
end
