import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapKernels
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueGroupRationality
import Mathlib.Tactic

/-!
# Actual realification uniqueness and transport (perfection) compatibility

Handoff Chapter 1 J5 asks for perfection/realification uniqueness.  This file
proves actual uniqueness statements that follow from the Frobenioid value kernel
laws and the actual finite-place valuation/degree data.

* `realification_unique_of_degree_eq`: the realification is uniquely determined
  by the degree homomorphism (Frobenioid law `degree_realification`); two value
  kernels with the same degree have the same realification.
* `realification_unique_of_degree_apply`: the pointwise form.
* `realification_transport_invariant`: the realification is invariant under the
  kernel transport (`transport_degree` plus `degree_realification`); this is the
  actual perfection-direction compatibility present in the kernel data.
* Concrete finite-place instances: the value-group and unit-level degree kernels
  of the prime strip have uniquely determined realifications once their degree
  homomorphism is fixed, and the unit-level realification is transport-invariant.

Missing source statement (reported, not frozen as done): the tree has no
source-specific perfection endomorphism of the value monoid with a
Frobenius-scaling law for its realification (a map phi with
`realification (phi x) = p * realification x` for the relevant prime p), and no
uniqueness statement for realification up to such a perfection.  Only the
transport invariance proved here is actual.  No card is asserted as completion.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField

universe u

variable {X : Type u} [CommMonoid X]

/-- Actual uniqueness: a Frobenioid value kernel's realification is determined
by its degree homomorphism. -/
theorem realification_unique_of_degree_eq
    (K L : FrobenioidValueKernel X) (h : forall x : X, K.degree x = L.degree x) :
    K.realification = L.realification := by
  funext x
  rw [← K.degree_realification x, ← L.degree_realification x, h x]

/-- Pointwise form of realification uniqueness from the degree data. -/
theorem realification_unique_of_degree_apply
    (K L : FrobenioidValueKernel X) (h : forall x : X, K.degree x = L.degree x)
    (x : X) : K.realification x = L.realification x :=
  congrFun (realification_unique_of_degree_eq K L h) x

/-- Actual perfection-direction compatibility: the realification is invariant
under the kernel transport, derived from `transport_degree` and
`degree_realification`. -/
theorem realification_transport_invariant
    (K : FrobenioidValueKernel X) (x : X) :
    K.realification (K.transport x) = K.realification x := by
  rw [← K.degree_realification (K.transport x), ← K.degree_realification x,
    K.transport_degree x]

/-- Concrete value-group uniqueness for the prime strip: any value kernel on
the finite-place value group with the actual degree of
`finitePlaceValueGroupKernel` has that kernel's realification. -/
theorem finitePlaceValueGroup_realification_unique
    (F : Type u) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (K : FrobenioidValueKernel (finitePlaceValueGroup))
    (h : forall x : finitePlaceValueGroup,
      K.degree x = (finitePlaceValueGroupKernel (F := F) v).degree x) :
    K.realification = (finitePlaceValueGroupKernel (F := F) v).realification :=
  realification_unique_of_degree_eq K (finitePlaceValueGroupKernel (F := F) v) h

/-- Concrete unit-level uniqueness for the prime strip: any value kernel on the
completion units with the actual degree of `finitePlaceUnitValueKernel` has
that kernel's realification. -/
theorem finitePlaceUnitValue_realification_unique
    (F : Type u) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (K : FrobenioidValueKernel (finitePlaceUnitValueMonoid (F := F) v))
    (h : forall x : finitePlaceUnitValueMonoid (F := F) v,
      K.degree x = (finitePlaceUnitValueKernel (F := F) v).degree x) :
    K.realification = (finitePlaceUnitValueKernel (F := F) v).realification :=
  realification_unique_of_degree_eq K (finitePlaceUnitValueKernel (F := F) v) h

/-- Concrete perfection-direction compatibility of the actual finite-place unit
kernel: its realification is transport-invariant. -/
theorem finitePlaceUnitValue_realification_transport_invariant
    (F : Type u) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (x : finitePlaceUnitValueMonoid (F := F) v) :
    (finitePlaceUnitValueKernel (F := F) v).realification
        ((finitePlaceUnitValueKernel (F := F) v).transport x) =
      (finitePlaceUnitValueKernel (F := F) v).realification x :=
  realification_transport_invariant (finitePlaceUnitValueKernel (F := F) v) x

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
end
