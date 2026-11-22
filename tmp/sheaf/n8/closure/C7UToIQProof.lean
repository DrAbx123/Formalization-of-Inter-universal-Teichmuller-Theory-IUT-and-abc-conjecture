import tmp.sheaf.n8.closure.C7Reductions
import tmp.sheaf.n8.closure.C7Native
import Mathlib

/-!
# C7 actual U-to-IQ proof target

This file records the actual map target from the C4 evaluation output to the C6
IQ carrier.  It does not use the constant-one weak donor and does not assume a
free map: the exact target carries both the evaluation compatibility and the
canonical-hull containment.  The single named sorry is the missing actual map.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7UToIQProof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native
open LeanFormal.IUT.N8Closure.C7DonorProof
open LeanFormal.IUT.N8Closure.C7Reductions
open LeanFormal.IUT.N8Closure.C7SourceU

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (T : SourceThetaIQInterface (I := I) C3)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- Exact actual map target: a map from the C4 value-point carrier to the C6
IQ carrier, compatible with the C4 evaluation and T.thetaImage, and carrying
the actual U region into the canonical IQ hull. -/
structure ActualSourceUToIQMap where
  toIQ : I.ThetaPilotPoint D.place.v →
    C6IQCarrier C3.tensorPlaces C3.tensorTuple
  eval_compat : ∀ c : SignedLabel l.value,
    toIQ (D.eval n x c) = T.thetaImage n c
  u_image_mem_canonicalHull : ∀ y ∈ sourceU (D := D) n x,
    toIQ y ∈ arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

/-- From the actual map, the source U-to-IQ donor follows with the actual
map, not a constant map. -/
theorem sourceUToIQDonor_of_actualMap
    (M : ActualSourceUToIQMap (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :
    SourceUToIQDonor (C3 := C3) (D := D) (n := n) (x := x) :=
  ⟨M.toIQ, M.u_image_mem_canonicalHull⟩

/-- From the actual map, theta-image containment follows from evaluation
compatibility and U image containment. -/
theorem thetaImageContainmentDonor_of_actualMap
    (M : ActualSourceUToIQMap (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :
    ThetaImageContainmentDonor (C3 := C3) T n := by
  intro c
  rw [← M.eval_compat c]
  exact M.u_image_mem_canonicalHull (D.eval n x c) ⟨c, rfl⟩

/-- Exact actual q-pilot membership target: the actual qPilotPoint lies in the
canonical IQ hull.  This is separate from the U map. -/
def ActualQPilotHullMembership : Prop :=
  ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
    arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple

/-- The exact q-pilot donor from the actual membership target. -/
theorem qPilotHullMembershipDonor_of_actualMembership
    (h : ActualQPilotHullMembership (C3 := C3)) :
    QPilotHullMembershipDonor (C3 := C3) :=
  h

end LeanFormal.IUT.N8Closure.C7UToIQProof
