import LeanFormal.IUT.ABCBridge.Geometry.RelativeCompletionFinrankReduction

/-!
# Instance registrations completing the local structure of finite-place completions

`FinitePlaceCompletionDegree` registers the algebra structures and scalar towers on the
completed local fields and rings, with two inputs (the finiteness of the upper completed
valuation ring over the lower one, gap-A, and the local-data comparison, gap-B) kept as
explicit hypotheses. Both inputs are proved unconditionally downstream: the comparison in
`FinitePlaceCompletionLocalInputs`, the finiteness in
`AdicCompletionValuationUniqueness`, with the integral-closure form and the unconditional
fundamental identities in `RelativeCompletionFinrankReduction`.

This module registers the two unconditional gap-A proofs as global type-class instances,
so that consumers of the conditional statements in `FinitePlaceCompletionDegree` (and of
Mathlib's local ramification and inertia theory on the completed rings) can discharge the
finiteness input by type-class inference:

* `Module.Finite O_v O_w`, from `moduleFinite_adicCompletionIntegers`;
* `IsIntegralClosure O_w O_v K_w`, from `isIntegralClosure_adicCompletionIntegers`.

No declaration of any imported module is modified; this file is a leaf of the import
order and is intended to be imported by consumers that want the unconditional shapes.
-/

universe u v

namespace LeanFormal.IUT

namespace NumberFieldFinitePlace

noncomputable section

variable {k : Type u} {K : Type v}
  [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- Gap-A of the finite-place completion degree reduction, registered as an instance: the
upper completed valuation ring is a finite module over the lower one. -/
instance instModuleFiniteAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    Module.Finite ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletionIntegers K) :=
  moduleFinite_adicCompletionIntegers (k := k) place

/-- The integral-closure form of gap-A, registered as an instance: the upper completed
valuation ring is the integral closure of the lower one in the upper completion. -/
instance instIsIntegralClosureAdicCompletionIntegers (place : NumberField.FinitePlace K) :
    IsIntegralClosure (place.maximalIdeal.adicCompletionIntegers K)
      ((comap (k := k) place).maximalIdeal.adicCompletionIntegers k)
      (place.maximalIdeal.adicCompletion K) :=
  isIntegralClosure_adicCompletionIntegers (k := k) place

end

end NumberFieldFinitePlace

end LeanFormal.IUT