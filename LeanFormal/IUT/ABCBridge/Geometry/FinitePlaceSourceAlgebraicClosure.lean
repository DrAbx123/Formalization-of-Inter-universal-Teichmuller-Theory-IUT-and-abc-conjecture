import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The actual arithmetic algebraic-closure carrier

Take the algebraic closure of the actual completed number field and give
it the spectral norm extending Qp. The underlying field is unchanged by
normalizing K_v. All algebraic towers and the Galois extension are
constructed. No completeness or properness of the algebraic closure is
assumed: finite subfields will supply the required complete carriers.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def SourceAlgebraicClosure (place : NumberField.FinitePlace K) :=
  AlgebraicClosure (NormalizedCompletion place)

instance sourceAlgebraicClosureField (place : NumberField.FinitePlace K) :
    Field (SourceAlgebraicClosure place) :=
  inferInstanceAs (Field (AlgebraicClosure (NormalizedCompletion place)))

instance sourceAlgebraicClosureCharZero (place : NumberField.FinitePlace K) :
    CharZero (SourceAlgebraicClosure place) :=
  inferInstanceAs (CharZero (AlgebraicClosure (NormalizedCompletion place)))

instance sourceAlgebraicClosureBaseAlgebra (place : NumberField.FinitePlace K) :
    Algebra (NormalizedCompletion place) (SourceAlgebraicClosure place) :=
  inferInstanceAs (Algebra (NormalizedCompletion place)
    (AlgebraicClosure (NormalizedCompletion place)))

instance sourceAlgebraicClosureIsAlgClosure (place : NumberField.FinitePlace K) :
    IsAlgClosure (NormalizedCompletion place) (SourceAlgebraicClosure place) :=
  inferInstanceAs (IsAlgClosure (NormalizedCompletion place)
    (AlgebraicClosure (NormalizedCompletion place)))

instance sourceAlgebraicClosurePadicAlgebra (place : NumberField.FinitePlace K) :
    Algebra (PadicScalarField place) (SourceAlgebraicClosure place) :=
  ((algebraMap (NormalizedCompletion place) (SourceAlgebraicClosure place)).comp
    (algebraMap (PadicScalarField place) (NormalizedCompletion place))).toAlgebra

instance sourceAlgebraicClosureScalarTower (place : NumberField.FinitePlace K) :
    IsScalarTower (PadicScalarField place) (NormalizedCompletion place)
      (SourceAlgebraicClosure place) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance sourceAlgebraicClosurePadicAlgebraic (place : NumberField.FinitePlace K) :
    Algebra.IsAlgebraic (PadicScalarField place) (SourceAlgebraicClosure place) :=
  Algebra.IsAlgebraic.trans (PadicScalarField place) (NormalizedCompletion place)
    (SourceAlgebraicClosure place)

instance sourceAlgebraicClosureNontriviallyNormedField (place : NumberField.FinitePlace K) :
    NontriviallyNormedField (SourceAlgebraicClosure place) :=
  spectralNorm.nontriviallyNormedField (PadicScalarField place) (SourceAlgebraicClosure place)

instance sourceAlgebraicClosureNormedAlgebra (place : NumberField.FinitePlace K) :
    NormedAlgebra (PadicScalarField place) (SourceAlgebraicClosure place) :=
  spectralNorm.normedAlgebra (PadicScalarField place) (SourceAlgebraicClosure place)

instance sourceAlgebraicClosureUltrametric (place : NumberField.FinitePlace K) :
    IsUltrametricDist (SourceAlgebraicClosure place) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  exact isNonarchimedean_spectralNorm

instance sourceAlgebraicClosureBaseNormedAlgebra (place : NumberField.FinitePlace K) :
    NormedAlgebra (NormalizedCompletion place) (SourceAlgebraicClosure place) :=
  spectralNorm.normedAlgebra' (PadicScalarField place) (NormalizedCompletion place)
    (SourceAlgebraicClosure place)

instance sourceAlgebraicClosureGalois (place : NumberField.FinitePlace K) :
    IsGalois (NormalizedCompletion place) (SourceAlgebraicClosure place) := by infer_instance

def sourceAlgebraicClosureRingEquiv (place : NumberField.FinitePlace K) :
    SourceAlgebraicClosure place ≃+* AlgebraicClosure (Completion place) := RingEquiv.refl _

end

end LeanFormal.IUT.NumberFieldFinitePlace
