import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# A normalized norm on the actual finite-place completion

The underlying field is the actual K_v. Its Qp-algebra is constructed in
FinitePlacePadicScalarStructure. The spectral norm gives the usual Qp
normalization, and finite dimensionality proves that its topology agrees
with the original completion topology. Integer-ring compatibility is a
separate theorem; a homeomorphism alone does not identify unit balls.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The same completed field, with its standard Qp-extended norm below. -/
def NormalizedCompletion (place : NumberField.FinitePlace K) := Completion place

instance normalizedCompletionField (place : NumberField.FinitePlace K) :
    Field (NormalizedCompletion place) := inferInstanceAs (Field (Completion place))

instance normalizedCompletionCharZero (place : NumberField.FinitePlace K) :
    CharZero (NormalizedCompletion place) := inferInstanceAs (CharZero (Completion place))

instance normalizedCompletionAlgebra (place : NumberField.FinitePlace K) :
    Algebra (PadicScalarField place) (NormalizedCompletion place) := padicCompletionAlgebra place

instance normalizedCompletionFinite (place : NumberField.FinitePlace K) :
    Module.Finite (PadicScalarField place) (NormalizedCompletion place) :=
  moduleFinite_padicCompletionAlgebra place

instance normalizedCompletionNontriviallyNormedField (place : NumberField.FinitePlace K) :
    NontriviallyNormedField (NormalizedCompletion place) :=
  spectralNorm.nontriviallyNormedField (PadicScalarField place) (NormalizedCompletion place)

instance normalizedCompletionNormedAlgebra (place : NumberField.FinitePlace K) :
    NormedAlgebra (PadicScalarField place) (NormalizedCompletion place) :=
  spectralNorm.normedAlgebra (PadicScalarField place) (NormalizedCompletion place)

instance normalizedCompletionUltrametric (place : NumberField.FinitePlace K) :
    IsUltrametricDist (NormalizedCompletion place) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  exact isNonarchimedean_spectralNorm

instance normalizedCompletionComplete (place : NumberField.FinitePlace K) :
    CompleteSpace (NormalizedCompletion place) :=
  spectralNorm.completeSpace (PadicScalarField place) (NormalizedCompletion place)

instance normalizedCompletionProper (place : NumberField.FinitePlace K) :
    ProperSpace (NormalizedCompletion place) :=
  FiniteDimensional.proper (PadicScalarField place) (NormalizedCompletion place)

/-- Identity on the underlying actual completed field; only the norm differs. -/
def normalizedCompletionRingEquiv (place : NumberField.FinitePlace K) :
    NormalizedCompletion place ≃+* Completion place := RingEquiv.refl _

/-- The normalized norm induces the actual completion topology. This is
proved from finite dimension and continuous original scalar multiplication. -/
def normalizedCompletionHomeomorph (place : NumberField.FinitePlace K) :
    NormalizedCompletion place ≃ₜ Completion place := by
  letI := padicCompletionAlgebra place
  letI := moduleFinite_padicCompletionAlgebra place
  letI := continuousSMul_padicCompletionAlgebra place
  let e : NormalizedCompletion place ≃ₗ[PadicScalarField place] Completion place :=
    LinearEquiv.refl _ _
  exact e.toContinuousLinearEquiv.toHomeomorph

theorem normalizedCompletionHomeomorph_apply (place : NumberField.FinitePlace K)
    (x : NormalizedCompletion place) :
    normalizedCompletionHomeomorph place x = normalizedCompletionRingEquiv place x := rfl

end

end LeanFormal.IUT.NumberFieldFinitePlace
