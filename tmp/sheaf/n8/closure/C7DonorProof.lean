import tmp.sheaf.n8.closure.C7Native
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullPullback
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullTransport
import Mathlib

/-!
# C7 donor proof / exact no-go

This file eliminates the weak sourceU-to-IQ donor by the actual canonical-hull
unit and reduces the theta-image and q-pilot donors to exact tensorLanding and
tensorUnit conditions.  It does not assume hull equality or choose a source map.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7DonorProof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldProductHull
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8Closure.C7Native

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

/-- The actual canonical hull contains the tensor unit 1. -/
theorem one_mem_arithmeticTupleCanonicalHull :
    (1 : ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) ∈
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  letI := Fintype.ofFinite C3.tensorIndex
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct C3.tensorPlaces C3.tensorTuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[C3.p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[C3.p] (E j)
  rw [arithmeticTupleCanonicalHull_eq C3.tensorPlaces C3.tensorTuple e]
  refine ⟨e 1, ?_, by simp⟩
  have h1 : (1 : ((j : J) → E j)) ∈
      hull (arithmeticTupleFieldLogImage C3.tensorPlaces C3.tensorTuple e) :=
    subset_hull _ ⟨1, one_mem_arithmeticTensorTupleLogRegion C3.tensorPlaces C3.tensorTuple,
      by simp⟩
  simpa using h1

/-- The weak sourceU donor is satisfiable by the canonical-hull unit.  This is
NOT a source-realized U -> IQ map; it only proves the donor Prop is nonempty. -/
theorem sourceUToIQDonor_weak :
    SourceUToIQDonor (C3 := C3) (D := D) (n := n) (x := x) :=
  ⟨fun _ => 1, fun _ _ => one_mem_arithmeticTupleCanonicalHull (C3 := C3)⟩

/-- Exact reduction of the theta-image donor to the tensorLanding condition. -/
theorem thetaImageContainmentDonor_iff_tensorLanding :
    ThetaImageContainmentDonor (C3 := C3) T n ↔
      ∀ j : SignedLabel l.value,
        C3.tensorLanding (T.thetaCompletion n j) ∈
          arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  unfold ThetaImageContainmentDonor
  constructor
  · intro h j
    rw [← T.thetaImage_eq n j]
    exact h j
  · intro h j
    rw [T.thetaImage_eq n j]
    exact h j

/-- Exact reduction of the q-pilot donor to membership of the actual tensor
unit. -/
theorem qPilotHullMembershipDonor_iff_tensorUnit :
    QPilotHullMembershipDonor (C3 := C3) ↔
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  unfold QPilotHullMembershipDonor
  rw [LeanFormal.IUT.N8Closure.C7Actual.qPilotPoint_eq_tensorUnit]

/-- Conditional q-pilot donor from the actual tensor unit being 1. -/
theorem qPilotHullMembershipDonor_of_tensorUnit_eq_one
    (h : (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) = 1) :
    QPilotHullMembershipDonor (C3 := C3) := by
  rw [qPilotHullMembershipDonor_iff_tensorUnit]
  rw [h]
  exact one_mem_arithmeticTupleCanonicalHull (C3 := C3)

end LeanFormal.IUT.N8Closure.C7DonorProof
