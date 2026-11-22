import tmp.sheaf.n8.closure.N8ClosureAchieved

/-!
# N8 full named-sorry closure from input

Constructs C3 from the C3 existence obligation and chooses the canonical Haar
measure on the resulting tensor block.  All missing data remain named sorries.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.Full

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
open LeanFormal.IUT.N8Closure.Final
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui uL uG uA uW u_1

variable {l : PrimeGeFive} {V : Type uv}

theorem n8_full_named_closure
    (A : C0ProductionAdditiveIndex.{ua})
    (L : LabelData.{uL})
    (transport : C0AdditiveLabelTransport A L)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D1 : C1ActualData I)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I
      (Multiplicative (Additive (Equiv.Perm L.Labels))))
    (C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uv, u_1} (l := l) (V := V) I) :
    Nonempty (N8FullOutput A L transport I C3 (c0Base A I)) := by
  letI : MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) :=
    borel _
  letI : BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) :=
    ⟨rfl⟩
  let mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) :=
    Measure.addHaar
  letI : Measure.IsAddHaarMeasure mu := inferInstance
  exact LeanFormal.IUT.N8Closure.Final.n8_named_closure A L transport I C3 mu inferInstance D1 C4

end LeanFormal.IUT.N8Closure.Full