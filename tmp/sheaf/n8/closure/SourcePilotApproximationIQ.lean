import tmp.sheaf.n8.closure.SourceDegreeComparisonIQ
import Mathlib

/-!
# C9 stage 2: actual IQ Values and q/theta approximation
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C9IQ

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
open LeanFormal.IUT.N8Closure.C8IQ

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

variable (T : SourceThetaIQInterface (I := I) C3)
variable (C7 : ∀ n : ThetaPilotCarrier l,
  SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n)

def muLogAt (T : SourceThetaIQInterface (I := I) C3)
    (C7 : ∀ n : ThetaPilotCarrier l, SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n)
    (n : ThetaPilotCarrier l) : ℝ :=
  iqSignedHullLogAt (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) (H := C7 n)

def degreeAt (T : SourceThetaIQInterface (I := I) C3)
    (C7 : ∀ n : ThetaPilotCarrier l, SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) n)
    (n : ThetaPilotCarrier l) : ℝ :=
  iqDegreeAt (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) (T := T) (n := n) (H := C7 n)

def Values : Set ℝ :=
  Set.range (fun n : ThetaPilotCarrier l => muLogAt (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 n)

def actual_values_bounded : Prop :=
  ∀ (n : ThetaPilotCarrier l) (y : ℝ), y ∈ Values (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 →
    y ≤ muLogAt (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 n

def actual_q_approximated : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (n : ThetaPilotCarrier l) (y : ℝ),
    y ∈ Values (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 ∧
    degreeAt (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 n - ε ≤ y

theorem sourcePilotApproximationIQ_stage2 :
    actual_values_bounded (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 ∧
    actual_q_approximated (C1 := C1) (C2 := C2) (C3 := C3) (D := D) (C5 := C5) (mu := mu) (B := B) T C7 := by
  sorry

end LeanFormal.IUT.N8Closure.C9IQ