import tmp.sheaf.n8.closure.SourceHolomorphicHull
noncomputable section
namespace ABCBridge.N8.C7Actual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
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
variable (T : SourceThetaIQInterface (I := I) C3)

def badHullB : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu where
  hull := ∅

theorem badHullB_iqHull_ne_empty :
    (badHullB (C3 := C3) (mu := mu)).iqInterface.hull ≠ ∅ := by
  have hpos := (measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (places := C3.tensorPlaces) (tuple := C3.tensorTuple) mu).1.1
  rw [show (badHullB (C3 := C3) (mu := mu)).iqInterface.hull =
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple by
    simp [badHullB, C6ActualIQData.iqInterface, arithmeticTupleIQHullLogVolumeInterface_hull]]
  intro h
  rw [h, measure_empty] at hpos
  exact lt_irrefl _ hpos

theorem no_hull_for_badHullB (T : SourceThetaIQInterface (I := I) C3) (n : ThetaPilotCarrier l) :
    ¬ Nonempty (SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := D) (C5 := C5) (mu := mu) (B := badHullB (C3 := C3) (mu := mu)) (T := T) n) := by
  rintro ⟨H⟩
  apply badHullB_iqHull_ne_empty (C3 := C3) (mu := mu)
  rw [H.iqHull_eq]
  rfl

end ABCBridge.N8.C7Actual
