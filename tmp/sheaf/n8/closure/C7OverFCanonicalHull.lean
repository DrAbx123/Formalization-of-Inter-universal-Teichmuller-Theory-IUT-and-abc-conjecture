import tmp.sheaf.n8.closure.C7QPilotActualAttempt
import tmp.sheaf.n8.closure.C7CanonicalUnitHullInclusionAttempt
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C3TensorConstruction
import Mathlib

/-!
# C7 over-F canonical hull

The native q lands in the actual tensor block of NativeTensorLandingDonor via
tensorLanding.  This block is the actual target used by the over-F/native q
data.  We define its canonical hull and unit reference from the production
donors, prove the unit-reference omission inclusion, and reduce the q landing
membership to the actual tensorUnit membership.

The remaining membership is the exact source gap; the F-completion vs Fmod
tensor-landing carrier mismatch is recorded, with no arbitrary hull or
membership.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7OverFCanonicalHull

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3TensorConstruction
open LeanFormal.IUT.N8Closure.C7QPilotActualAttempt
open LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable (L : NativeTensorLandingDonor X)

/-- The actual canonical hull of the native tensor target. -/
abbrev overFCanonicalHull :
    Set (ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) :=
  arithmeticTupleCanonicalHull L.tensorPlaces L.tensorTuple

/-- The actual canonical unit reference of the native tensor target. -/
abbrev overFCanonicalUnitReference :
    Set (ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) :=
  arithmeticTupleCanonicalUnitReference L.tensorPlaces L.tensorTuple

/-- Actual inclusion of the canonical unit reference in the canonical hull. -/
theorem overFCanonicalUnitReference_subset_canonicalHull :
    (overFCanonicalUnitReference (L := L) : Set (ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple)) ⊆
      overFCanonicalHull (L := L) :=
  arithmeticTupleCanonicalUnitReference_subset_canonicalHull L.tensorPlaces L.tensorTuple

/-- The over-F/native q landing membership target: the q tensor landing lies in
the actual canonical hull. -/
def OverFTensorUnitMembership : Prop :=
  (L.tensorUnit : ArithmeticTensorTupleBlock L.tensorPlaces L.tensorTuple) ∈
    overFCanonicalHull (L := L)

/-- The q landing membership is exactly the actual tensorUnit membership
(tensorLanding_q). -/
theorem overF_q_landing_mem_iff_tensorUnit_mem (D : NativeQDonor X) :
    L.tensorLanding (nativeQ X D).q ∈ overFCanonicalHull (L := L) ↔
      OverFTensorUnitMembership (L := L) := by
  unfold OverFTensorUnitMembership overFCanonicalHull
  rw [← L.tensorLanding_q D]

/-- Conditional q landing membership from the actual tensorUnit membership. -/
theorem overF_q_landing_mem_of_tensorUnit (D : NativeQDonor X)
    (h : OverFTensorUnitMembership (L := L)) :
    L.tensorLanding (nativeQ X D).q ∈ overFCanonicalHull (L := L) :=
  (overF_q_landing_mem_iff_tensorUnit_mem (X := X) (L := L) D).mpr h

/-- Decisive no-go form: the q landing membership reduces to the actual
tensorUnit membership; the latter is not a frozen-field consequence, and the
native q completion is over F while tensorLanding's tensor places are over
Fmod.  No production bridge/integrality theorem supplies it. -/
theorem overF_q_landing_membership_is_source_obligation (D : NativeQDonor X) :
    L.tensorLanding (nativeQ X D).q ∈ overFCanonicalHull (L := L) ↔
      OverFTensorUnitMembership (L := L) :=
  overF_q_landing_mem_iff_tensorUnit_mem (X := X) (L := L) D

end LeanFormal.IUT.N8Closure.C7OverFCanonicalHull
