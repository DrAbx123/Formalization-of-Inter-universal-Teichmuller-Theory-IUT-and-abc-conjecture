import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegree
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension
import LeanFormal.IUT.IUTII.Frobenioid.Example36PacketNumberField
import tmp.sheaf.xif.paper.S3132ConcreteGaussianPlaceSpecActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PacketNumberFieldConstruction
open LeanFormal.IUT.XiFPaper.S3132ConcreteGaussianPlaceSpecActual

namespace LeanFormal.IUT.XiFPaper.S3132CompletionMapSurjectiveActual

/-!
# task-65 (1): the manufactured surjectivity/dimension step for the completionMap

**Component, not a paper object.**  Owner: hull.  Consumers: the concrete
Example 3.6 fiber equivalence; mainline registry.

The tree's completion embedding `completionMap (k := Q) place` is injective
(`completionMap_injective`), and the global algebra structure
`instAlgebraAdicCompletion` has `algebraMap = completionMap`
(`algebraMap_instAlgebraAdicCompletion`), with `Module.Finite` available
(`moduleFinite_completionAlgebra`).  If the local degree is one
(`Module.finrank lower upper = 1`, e.g.
`concreteGaussianFivePlace_completion_finrank_eq_one` for the concrete Gaussian
place), then the domain and codomain finranks agree
(`Module.finrank lower lower = 1`), so mathlib's
`LinearMap.injective_iff_surjective_of_finrank_eq_finrank` turns injectivity
into surjectivity.  This is the single manufactured dimension step; the finrank
theorem and the algebra map use the same global instance, so there is no module
structure mismatch.

Pages: IUT III, Proposition 3.2, (ii), pp. 97-99; Proposition 3.7, (ii), (v),
pp. 108-112.
-/

/-- **Manufactured step:** an injective completion map of local degree one is
surjective (dimension/rank-nullity). -/
theorem completionMap_surjective_of_finrank_one
    {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    (place : NumberField.FinitePlace K)
    (hfin : Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K) = 1) :
    Function.Surjective (completionMap (k := k) place) := by
  haveI : Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K) :=
    moduleFinite_completionAlgebra (k := k) place
  have hinj : Function.Injective (algebraMap
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K)) := by
    rw [algebraMap_instAlgebraAdicCompletion (k := k) place]
    exact completionMap_injective (k := k) place
  have hdom : Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
      ((comap (k := k) place).maximalIdeal.adicCompletion k) = 1 :=
    CommSemiring.finrank_self _
  have H : Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
      ((comap (k := k) place).maximalIdeal.adicCompletion k) =
        Module.finrank ((comap (k := k) place).maximalIdeal.adicCompletion k)
          (place.maximalIdeal.adicCompletion K) := by
    rw [hdom, hfin]
  have hinj_lin : Function.Injective (Algebra.linearMap
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K)) := hinj
  have hsurj_lin : Function.Surjective (Algebra.linearMap
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := (comap (k := k) place).maximalIdeal.adicCompletion k)
      (V := (comap (k := k) place).maximalIdeal.adicCompletion k)
      (V₂ := place.maximalIdeal.adicCompletion K) H
      (f := Algebra.linearMap
        ((comap (k := k) place).maximalIdeal.adicCompletion k)
        (place.maximalIdeal.adicCompletion K))).mp hinj_lin
  have hsurj : Function.Surjective (algebraMap
      ((comap (k := k) place).maximalIdeal.adicCompletion k)
      (place.maximalIdeal.adicCompletion K)) := hsurj_lin
  rwa [algebraMap_instAlgebraAdicCompletion (k := k) place] at hsurj

/-- **Concrete packet place:** the rational-to-packet completion map is
surjective. -/
theorem packet_completionMap_surjective :
    Function.Surjective (completionMap (k := ℚ) packetFinitePlace) :=
  completionMap_surjective_of_finrank_one (k := ℚ) packetFinitePlace
    packet_completion_finrank_eq_one

/-- **Unconditional concrete fiber ring equivalence:** the rational completion at
5 is ring-isomorphic to the concrete packet completion. -/
theorem concreteGaussianFiberRingEquiv_unconditional :
    Nonempty (Completion (NumberFieldFinitePlace.comap (k := ℚ) packetFinitePlace) ≃+*
      packetFiniteCompletion) :=
  concreteGaussianFiberRingEquiv_of_surjective packet_completionMap_surjective

#check completionMap_surjective_of_finrank_one
#check packet_completionMap_surjective
#check concreteGaussianFiberRingEquiv_unconditional

end LeanFormal.IUT.XiFPaper.S3132CompletionMapSurjectiveActual

end