import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.n8.closure.C7Actual
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-!
# C7 actual Haar mass positivity and finiteness

On the actual canonical hull of C6ActualIQData.actual, prove
`0 < mu H` and `mu H < top`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7HaarActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]

theorem actual_canonicalHull_haar_pos :
    0 < mu (arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple) :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) mu).1.1

theorem actual_canonicalHull_haar_lt_top :
    mu (arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) mu).1.2

theorem actual_commonHull_haar_pos :
    0 < mu (commonHull (C3 := C3) mu (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)) :=
  actual_canonicalHull_haar_pos (C3 := C3) (mu := mu)

theorem actual_commonHull_haar_lt_top :
    mu (commonHull (C3 := C3) mu (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)) < ⊤ :=
  actual_canonicalHull_haar_lt_top (C3 := C3) (mu := mu)

/-- Conditional C7 obligations for the actual canonical hull: the only
remaining inputs are theta-image containment and qPilot membership. -/
def actualC7Obligations
    (hImage : permittedImage (I := I) (C3 := C3) T n ⊆
      commonHull (C3 := C3) mu (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu))
    (hq : ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
      commonHull (C3 := C3) mu (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)) :
    LeanFormal.IUT.N8Closure.C7Actual.C7ActualObligations (C3 := C3) (mu := mu)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) (T := T) (n := n) where
  iqHull_eq := by
    simp [commonHull, C6ActualIQData.actual]
  thetaImage_subset_hull := hImage
  qPilot_mem := hq
  haar_pos := actual_commonHull_haar_pos (C3 := C3) (mu := mu)
  haar_lt_top := actual_commonHull_haar_lt_top (C3 := C3) (mu := mu)

end LeanFormal.IUT.N8Closure.C7HaarActual