import tmp.sheaf.n8.closure.C7DonorProof
import tmp.sheaf.n8.closure.C7Native
import Mathlib

/-!
# C7 exact reductions and U-to-IQ donor

This file strengthens the C7 reductions:
- q-pilot membership is exactly tensor-unit membership;
- theta-image containment is exactly pointwise tensorLanding containment;
- the actual U-to-IQ donor is reduced to an exact map obligation and a
  theta-image fiber-constancy condition.  No map is assumed and no hull
  equality is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7Reductions

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

/-- Set-level q-pilot reduction: membership of qPilotPoint is exactly
membership of the actual tensor unit. -/
theorem qPilot_mem_canonicalHull_iff_tensorUnit_mem :
    ABCBridge.N8.C7Actual.qPilotPoint (C3 := C3) ∈
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple ↔
      (C3.tensorUnit : C6IQCarrier C3.tensorPlaces C3.tensorTuple) ∈
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  rw [LeanFormal.IUT.N8Closure.C7Actual.qPilotPoint_eq_tensorUnit]

/-- Set-level theta reduction: the permitted image lies in the actual
canonical hull exactly when every T.thetaImage does. -/
theorem permittedImage_subset_canonicalHull_iff_thetaImage :
    permittedImage (I := I) (C3 := C3) T n ⊆
        arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple ↔
      ∀ j : SignedLabel l.value,
        T.thetaImage n j ∈
          arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple := by
  constructor
  · intro h j
    exact h ⟨j, rfl⟩
  · rintro h y ⟨j, rfl⟩
    exact h j

/-- The exact actual U-to-IQ map obligation: a map on source points which
agrees with T.thetaImage on the U family and carries U into the canonical hull.
No map is assumed; this is the exact missing declaration. -/
def SourceUToIQMapObligation : Prop :=
  ∃ toIQ : I.ThetaPilotPoint D.place.v →
      C6IQCarrier C3.tensorPlaces C3.tensorTuple,
    (∀ y ∈ sourceU (D := D) n x,
      toIQ y ∈ arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple) ∧
    (∀ c : SignedLabel l.value,
      toIQ (D.eval n x c) = T.thetaImage n c)

/-- The exact actual U-to-IQ map obligation implies theta containment. -/
theorem thetaImageContainmentDonor_of_sourceUToIQMapObligation
    (h : SourceUToIQMapObligation (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :
    ThetaImageContainmentDonor (C3 := C3) T n := by
  obtain ⟨toIQ, hU, htheta⟩ := h
  intro c
  rw [← htheta c]
  exact hU (D.eval n x c) ⟨c, rfl⟩

/-- The theta-image fiber-constancy condition on the actual C4 evaluation:
if two choices evaluate to the same source point, their theta images agree.
This is the exact condition needed to descend T.thetaImage to U. -/
def ThetaImageFiberConstant : Prop :=
  ∀ c c' : SignedLabel l.value,
    D.eval n x c = D.eval n x c' → T.thetaImage n c = T.thetaImage n c'

/-- Construction of an actual U-to-IQ map from theta containment plus fiber
constancy.  The map is defined on U by the chosen choice and is 1 outside U;
it is not a free parameter. -/
theorem sourceUToIQMapObligation_of_thetaDonor_fiberConstant
    (hTheta : ThetaImageContainmentDonor (C3 := C3) T n)
    (hfiber : ThetaImageFiberConstant (C3 := C3) (D := D) (T := T) (n := n) (x := x)) :
    SourceUToIQMapObligation (C3 := C3) (D := D) (T := T) (n := n) (x := x) := by
  classical
  let toIQ : I.ThetaPilotPoint D.place.v →
      C6IQCarrier C3.tensorPlaces C3.tensorTuple :=
    fun y => if hy : y ∈ sourceU (D := D) n x then
      T.thetaImage n (Classical.choose hy) else 1
  refine ⟨toIQ, ?_, ?_⟩
  · intro y hy
    simp only [toIQ, dif_pos hy]
    exact hTheta _
  · intro c
    have hc : D.eval n x c ∈ sourceU (D := D) n x := ⟨c, rfl⟩
    simp only [toIQ, dif_pos hc]
    apply hfiber
    exact Classical.choose_spec hc

end LeanFormal.IUT.N8Closure.C7Reductions
