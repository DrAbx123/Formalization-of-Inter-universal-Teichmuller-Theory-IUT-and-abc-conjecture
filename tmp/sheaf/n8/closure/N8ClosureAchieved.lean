import tmp.sheaf.n8.closure.N8Closure
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.IPLFamilyData
import tmp.sheaf.n8.closure.C2Actual

/-!
# N8 named-sorry closure assembly

Assembles the C10 target from the existing C1-C9 components.  Missing C4/C5
existence data are named theorem-level sorries; C7 is supplied by the C7
stage-2 obligation.  No total-goal sorry.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.Final

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.TargetSignature
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.LabelData
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.C8IQ
open LeanFormal.IUT.N8Closure.C9IQ
open LeanFormal.IUT.N8Closure.C10Full
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe ua uv upi umon ui uL uG uA uW u_1

variable {l : PrimeGeFive} {V : Type uv}

/-- Local C1 actual-data package: the four source data needed to build C1. -/
structure C1ActualData (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  placeEquiv : V ≃ NumberFieldPlaceIndex (F := I.initial.arithmetic.Fmod)
  selected : V
  selected_realization : I.SourceImageRealization selected
  fiberMonEquiv : ∀ (n m : Int) (v : V),
    (I.primeStripAt n m).Mon v ≃*
      SourcePlaceValueGroup (F := I.initial.arithmetic.Fmod) (placeEquiv v)

def sourceInputBindingOfActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (D : C1ActualData I) :
    SourceInputBinding I where
  place :=
    { placeEquiv := D.placeEquiv
      selected := D.selected
      selected_realization := D.selected_realization
      fiberMonEquiv := D.fiberMonEquiv }

/-- N8 named-sorry closure: construct C1-C7 from the existing existence
obligations and call the C10 assembly.  C3 remains an explicit input here;
the C0 base is the only C0 call inside C10. -/
theorem n8_named_closure
    (A : C0ProductionAdditiveIndex.{ua})
    (L : LabelData.{uL})
    (transport : C0AdditiveLabelTransport A L)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uv, u_1} (l := l) (V := V) I)
    [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
    (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
    (hmu : Measure.IsAddHaarMeasure mu)
    (D1 : C1ActualData I)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I
      (Multiplicative (Additive (Equiv.Perm L.Labels)))) :
    Nonempty (N8FullOutput A L transport I C3 (c0Base A I)) := by
  letI : Measure.IsAddHaarMeasure mu := hmu
  let C1 : SourceInputBinding I := sourceInputBindingOfActual I D1
  let C2 : SourceLogKummerData I C1 := Classical.choice (LeanFormal.IUT.N8Closure.C2Actual.sourceLogKummerData_nonempty_actual I C1)
  -- C4 supplied as an explicit source datum
  let IPL : IPLFamilyData I := Classical.choice (iplFamilyData_nonempty I)
  let C5 : SourceAlgorithmCompatibilityData
      (LAdd := Additive (Equiv.Perm L.Labels)) I C1 C2 C3 C4 :=
    Classical.choice (sourceAlgorithmCompatibility_nonempty I C1 C2 C3 C4)
  let C7 : ∀ n : ThetaPilotCarrier l,
      SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
        (D := C4) (C5 := C5) (mu := mu)
        (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)
        (T := LeanFormal.IUT.N8Closure.C10Full.thetaT C3) n :=
    fun n => Classical.choice
      (sourceHolomorphicHullData_nonempty (C1 := C1) (C2 := C2) (C3 := C3)
        (D := C4) (C5 := C5) (mu := mu)
        (B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple mu)
        (T := LeanFormal.IUT.N8Closure.C10Full.thetaT C3) n)
  exact n8Assembly_closure A L transport I C1 C2 C3 C4 IPL C5 mu C7

end LeanFormal.IUT.N8Closure.Final