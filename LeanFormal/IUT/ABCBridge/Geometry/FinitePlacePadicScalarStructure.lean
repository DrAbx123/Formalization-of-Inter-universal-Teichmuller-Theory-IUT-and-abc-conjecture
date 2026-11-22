import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# Actual p-adic scalar structure on a number-field completion

The rational finite-place completion is continuously isomorphic to Qp.
Composing its inverse with the already constructed completion embedding
gives the Qp-algebra structure on the actual K_v, with finite dimension
and continuous scalar action in the original completion topology.

The canonical completion norm need not restrict to the usual Qp norm.
This file does not assert a NormedAlgebra instance for that norm: the
normalized norm and its compatibility are subsequent mathematical steps.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The rational prime underneath the actual finite place. -/
def completionRationalPrime (place : NumberField.FinitePlace K) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (comap (k := ℚ) place).maximalIdeal

instance completionRationalPrime_fact (place : NumberField.FinitePlace K) :
    Fact (completionRationalPrime place).val.Prime := ⟨(completionRationalPrime place).property⟩

abbrev PadicScalarField (place : NumberField.FinitePlace K) :=
  ℚ_[(completionRationalPrime place).val]

/-- The existing continuous isomorphism, at this actual contracted place. -/
def rationalCompletionPadicEquiv (place : NumberField.FinitePlace K) :
    Completion (comap (k := ℚ) place) ≃A[ℚ] PadicScalarField place :=
  Rat.HeightOneSpectrum.adicCompletion.padicEquiv (comap (k := ℚ) place).maximalIdeal

/-- The actual Qp embedding in K_v, not an input on a source structure. -/
def padicCompletionHom (place : NumberField.FinitePlace K) :
    PadicScalarField place →+* Completion place :=
  (completionMap (k := ℚ) place).comp
    (rationalCompletionPadicEquiv place).symm.toAlgEquiv.toRingHom

abbrev padicCompletionAlgebra (place : NumberField.FinitePlace K) :
    Algebra (PadicScalarField place) (Completion place) :=
  (padicCompletionHom place).toAlgebra

theorem padicCompletionAlgebra_algebraMap (place : NumberField.FinitePlace K) :
    letI := padicCompletionAlgebra place
    algebraMap (PadicScalarField place) (Completion place) = padicCompletionHom place := rfl

theorem continuous_padicCompletionHom (place : NumberField.FinitePlace K) :
    Continuous (padicCompletionHom place) :=
  (continuous_completionMap (k := ℚ) place).comp
    (rationalCompletionPadicEquiv place).symm.continuous

/-- Finite dimension is transported across the actual rational-completion
isomorphism and composed with the proved finite completion extension. -/
theorem moduleFinite_padicCompletionAlgebra (place : NumberField.FinitePlace K) :
    letI := padicCompletionAlgebra place
    Module.Finite (PadicScalarField place) (Completion place) := by
  let R := Completion (comap (k := ℚ) place)
  letI : Algebra (PadicScalarField place) R :=
    (rationalCompletionPadicEquiv place).symm.toAlgEquiv.toRingHom.toAlgebra
  letI := completionAlgebra (k := ℚ) place
  letI := padicCompletionAlgebra place
  letI : IsScalarTower (PadicScalarField place) R (Completion place) :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite (PadicScalarField place) R :=
    Module.Finite.of_surjective (Algebra.linearMap (PadicScalarField place) R)
      (rationalCompletionPadicEquiv place).symm.surjective
  letI := moduleFinite_completionAlgebra (k := ℚ) place
  exact Module.Finite.trans R (Completion place)

/-- Scalar multiplication is continuous for the original completion
topology, before any replacement of its norm by the normalized one. -/
theorem continuousSMul_padicCompletionAlgebra (place : NumberField.FinitePlace K) :
    letI := padicCompletionAlgebra place
    ContinuousSMul (PadicScalarField place) (Completion place) := by
  letI := padicCompletionAlgebra place
  refine ⟨?_⟩
  change Continuous (fun a : PadicScalarField place × Completion place =>
    padicCompletionHom place a.1 * a.2)
  exact ((continuous_padicCompletionHom place).comp continuous_fst).mul continuous_snd

end

end LeanFormal.IUT.NumberFieldFinitePlace
