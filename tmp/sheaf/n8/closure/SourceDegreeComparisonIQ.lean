import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.C6ActualIQData
import Mathlib

/-!
# C8 stage 2: actual IQ degree/mu_log comparison on the C7 hull
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C8IQ

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable (C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 D)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu)


def iqHullLogVolume : ENNReal :=
  B.iqInterface.logVolume (commonHull (C3 := C3) mu B)

theorem iqHullLogVolume_eq
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) :
    iqHullLogVolume (C3 := C3) (mu := mu) B =
      B.iqInterface.logVolume B.iqInterface.hull := by
  unfold iqHullLogVolume
  rw [← H.iqHull_eq]

def iqMuLog : ℝ := (iqHullLogVolume (C3 := C3) (mu := mu) B).toReal

def iqDegree : ℝ := B.normalizedLogVolume (commonHull (C3 := C3) mu B)

def iqSignedHullLog : ℝ := B.signedHullLog

def iqMuLogAt (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) : ℝ :=
  iqMuLog (C3 := C3) (mu := mu) B

def iqDegreeAt (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) : ℝ :=
  iqDegree (C3 := C3) (mu := mu) B

def iqSignedHullLogAt (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l)
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n) : ℝ :=
  B.signedHullLog

theorem sourceDegreeComparisonIQ
    (T : SourceThetaIQInterface (I := I) C3)
    (n : ThetaPilotCarrier l)
    (H : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu)
      (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) (T := T) n) :
    iqDegree (C3 := C3) (mu := mu)
        (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu) =
      (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).normalizationWeight *
        ((C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).signedHullLog -
          (C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu).unitReferenceLog) := by
  rfl

end LeanFormal.IUT.N8Closure.C8IQ