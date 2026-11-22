import tmp.sheaf.n8.closure.SourceDegreeFromSource
import tmp.sheaf.n8.closure.C7ActualFromSource

/-! # Complete SourceDegree paper-source packet

Task-538 write-only construction.  This packet bundles the C3 context with
the four explicit paper/source components:

* `PaperNormalizationSourceData` (lambda/tuple/procession/global-volume
  fields; treated as explicit paper source data, not theorems);
* `C6ProductVolumeData`;
* `C3ConcreteHullObligations` (the two exact C7 containment primitives);
* the C1/C2/C3/D/C5/Dalg/C5Alg/T/n context needed by the consumers.

From one packet it derives:

* the concrete `PaperNormalizedVolumeData` term;
* the concrete C7 `SourceHolomorphicHullData` from the hull obligations;
* the C3 SourceDegree residual equivalence with actual arithmetic degree =
  C6 normalized hull log-volume;
* both directions of that equivalence.

No arbitrary weights/constants, `PUnit`, `True`, `sorry`, or axiom is used.
The paper fields are structure fields, not asserted theorems.
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
open LeanFormal.IUT.N8Closure.C7FromSource
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

/-- The complete SourceDegree paper-source packet. -/
structure SourceDegreePaperSourcePacket
    (C3 : SourcePilotRegionData (l := l) (V := V0) I)
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    {LAdd : Type uG} [AddGroup LAdd]
    {Dalg : SourceWitnessedOutputData (l := l) (V := V0) I (Multiplicative LAdd)}
    {C5Alg : SourceAlgorithmCompatibilityData I C1 C2 C3 Dalg}
    {muIQ : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
    [Measure.IsAddHaarMeasure muIQ]
    {T : SourceThetaIQInterface (I := I) C3}
    {n : ThetaPilotCarrier l} where
  /-- Explicit paper normalization/procession/global-volume source data. -/
  paper : PaperNormalizationSourceData C3.tensorPlaces C3.tensorTuple muIQ
  /-- Explicit C6 product-volume source data. -/
  c6Product : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v)
  /-- The two exact C7 hull containment obligations. -/
  hullObligations : C3ConcreteHullObligations (C3 := C3) (mu := muIQ) T n

namespace SourceDegreePaperSourcePacket

variable {C3 : SourcePilotRegionData (l := l) (V := V0) I}
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable {LAdd : Type uG} [AddGroup LAdd]
variable {Dalg : SourceWitnessedOutputData (l := l) (V := V0) I (Multiplicative LAdd)}
variable {C5Alg : SourceAlgorithmCompatibilityData I C1 C2 C3 Dalg}
variable {muIQ : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
variable [Measure.IsAddHaarMeasure muIQ]
variable {T : SourceThetaIQInterface (I := I) C3}
variable {n : ThetaPilotCarrier l}

variable (P : SourceDegreePaperSourcePacket (l := l) (V0 := V0) (Label := Label)
  (I := I) (D := D) (C5 := C5) (C1 := C1) (C2 := C2) C3 (LAdd := LAdd)
  (Dalg := Dalg) (C5Alg := C5Alg) (muIQ := muIQ) (T := T) (n := n))

/-- Concrete paper normalized-volume term carried by the packet. -/
def paperNormalizedVolumeData :
    PaperNormalizedVolumeData C3.tensorPlaces C3.tensorTuple muIQ :=
  P.paper.toPaperNormalizedVolumeData

@[simp] theorem paperNormalizedVolumeData_localVolume :
    P.paperNormalizedVolumeData.localVolume =
      paperLocalVolumeActual C3.tensorPlaces C3.tensorTuple muIQ := rfl

@[simp] theorem paperNormalizedVolumeData_lambdaData :
    P.paperNormalizedVolumeData.lambdaData = P.paper.lambdaData := rfl

@[simp] theorem paperNormalizedVolumeData_globalVolume :
    P.paperNormalizedVolumeData.globalVolume = P.paper.globalVolume := rfl

/-- Concrete C7 hull data derived from the packet's exact containment
obligations. -/
def c7HullData :
    SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ)
      (T := T) n :=
  concreteSourceHolomorphicHullData (C1 := C1) (C2 := C2)
    (C3 := C3) (D := Dalg) (C5 := C5Alg) (mu := muIQ)
    (T := T) (n := n) P.hullObligations

@[simp] theorem c7HullData_iqHull_eq :
    P.c7HullData.iqHull_eq =
      actual_iqHull_eq (C3 := C3) (mu := muIQ) := rfl

@[simp] theorem c7HullData_image_subset_hull :
    P.c7HullData.image_subset_hull = P.hullObligations.thetaImage_subset_hull := rfl

@[simp] theorem c7HullData_qPilot_mem :
    P.c7HullData.qPilot_mem = P.hullObligations.qPilot_mem := rfl

/-- C3 SourceDegree residual equivalence from one paper-source packet. -/
theorem residual_iff_actualDegree_eq_BHull :
    SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      P.paperNormalizedVolumeData P.c6Product P.c7HullData ↔
      actualArithmeticDegree
        (K := I.initial.arithmetic.Fmod) (p := C3.p)
        (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
        (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
        P.paperNormalizedVolumeData =
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull := by
  simpa [paperNormalizedVolumeData, c7HullData] using
    sourceDegreeResidual_iff_actualDegree_eq_BHull_c3_fromSourceHull
      (C3 := C3) (muIQ := muIQ) (C1 := C1) (C2 := C2)
      (D := D) (C5 := C5) (Dalg := Dalg) (C5Alg := C5Alg)
      (T := T) (n := n) (C6Prod := P.c6Product)
      P.paper P.hullObligations

/-- Forward direction: actual degree = C6 hull volume gives the residual. -/
theorem residual_of_actualDegree_eq_BHull
    (h : actualArithmeticDegree
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      P.paperNormalizedVolumeData =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull) :
    SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      P.paperNormalizedVolumeData P.c6Product P.c7HullData :=
  P.residual_iff_actualDegree_eq_BHull.mpr h

/-- Reverse direction: the residual gives actual degree = C6 hull volume. -/
theorem actualDegree_eq_BHull_of_residual
    (h : SourceDegreeComparisonResidual
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      P.paperNormalizedVolumeData P.c6Product P.c7HullData) :
    actualArithmeticDegree
      (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (iota := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      (places := C3.tensorPlaces) (tuple := C3.tensorTuple) (mu := muIQ)
      P.paperNormalizedVolumeData =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).normalizedLogVolume
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple muIQ).hull :=
  P.residual_iff_actualDegree_eq_BHull.mp h

end SourceDegreePaperSourcePacket

end LeanFormal.IUT.N8Closure.C8

end
