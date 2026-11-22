import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import LeanFormal.IUT.Foundations.LocalFields.ContinuousPadicRingHom

/-!
# The actual relative completed-field embedding over the same Qp

The old completed-field map is unchanged as a ring homomorphism. Its
continuity is transported along the proved normalized-completion
homeomorphisms. Rational density proves Qp compatibility; the original
finite relative extension supplies finiteness over the lower completion.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

noncomputable section

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
variable {p : ℕ} [Fact p.Prime]

instance commonPrimeCompletionPadicModule (place : FinitePlaceAtPrime K p) :
    Module ℚ_[p] (CommonPrimeCompletion place) :=
  (inferInstance : NormedSpace ℚ_[p] (CommonPrimeCompletion place)).toModule

theorem commonPrimeCompletion_moduleActionEquality (place : FinitePlaceAtPrime K p) :
    (inferInstance : Module ℚ_[p] (CommonPrimeCompletion place)).toSMul =
      (commonPrimeCompletionAlgebra place).toSMul := by
  rcases place with ⟨place, hprime⟩
  cases hprime
  rfl

def commonPrimeCompletionActualHomeomorph (place : FinitePlaceAtPrime K p) :
    CommonPrimeCompletion place ≃ₜ Completion place.val :=
  normalizedCompletionHomeomorph place.val

theorem continuous_commonPrimeCompletionAlgebraMap (place : FinitePlaceAtPrime K p) :
    Continuous (algebraMap ℚ_[p] (CommonPrimeCompletion place)) :=
  continuous_algebraMap ℚ_[p] (CommonPrimeCompletion place)

def relativeNormalizedCompletionRingHom (place : FinitePlaceAtPrime K p) :
    CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place) →+*
      CommonPrimeCompletion place :=
  completionMap place.val

omit [Fact p.Prime] in
theorem continuous_relativeNormalizedCompletionRingHom (place : FinitePlaceAtPrime K p) :
    Continuous (relativeNormalizedCompletionRingHom (k := k) place) :=
  (commonPrimeCompletionActualHomeomorph place).symm.continuous.comp
    ((continuous_completionMap place.val).comp
      (commonPrimeCompletionActualHomeomorph (relativeCommonPrimePlace (k := k) place)).continuous)

theorem relativeNormalizedCompletion_commutes (place : FinitePlaceAtPrime K p) (a : ℚ_[p]) :
    relativeNormalizedCompletionRingHom (k := k) place
      (algebraMap ℚ_[p] (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place)) a) =
      algebraMap ℚ_[p] (CommonPrimeCompletion place) a :=
  LocalFieldPadicScalars.continuousRingHom_commutes (p := p)
    (E := CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
    (F := CommonPrimeCompletion place)
    (relativeNormalizedCompletionRingHom (k := k) place)
    (continuous_relativeNormalizedCompletionRingHom (k := k) place)
    (continuous_commonPrimeCompletionAlgebraMap (relativeCommonPrimePlace (k := k) place))
    (continuous_commonPrimeCompletionAlgebraMap place) a

def relativeNormalizedCompletionAlgHom (place : FinitePlaceAtPrime K p) :
    CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place) →ₐ[ℚ_[p]]
      CommonPrimeCompletion place where
  toRingHom := relativeNormalizedCompletionRingHom (k := k) place
  commutes' := relativeNormalizedCompletion_commutes (k := k) place

instance relativeNormalizedCompletionAlgebra (place : FinitePlaceAtPrime K p) :
    Algebra (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
      (CommonPrimeCompletion place) :=
  (relativeNormalizedCompletionRingHom (k := k) place).toAlgebra

instance relativeNormalizedCompletionScalarTower (place : FinitePlaceAtPrime K p) :
    IsScalarTower ℚ_[p] (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
      (CommonPrimeCompletion place) := by
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change algebraMap ℚ_[p] (CommonPrimeCompletion place) a =
    relativeNormalizedCompletionRingHom (k := k) place
      (algebraMap ℚ_[p] (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place)) a)
  exact (relativeNormalizedCompletion_commutes (k := k) place a).symm

theorem relativeNormalizedCompletionModuleTower (place : FinitePlaceAtPrime K p) :
    @IsScalarTower ℚ_[p]
      (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
      (CommonPrimeCompletion place)
      (inferInstance : Module ℚ_[p]
        (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))).toSMul
      (inferInstance : Module
        (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
        (CommonPrimeCompletion place)).toSMul
      (inferInstance : Module ℚ_[p] (CommonPrimeCompletion place)).toSMul := by
  rw [commonPrimeCompletion_moduleActionEquality,
    commonPrimeCompletion_moduleActionEquality]
  exact relativeNormalizedCompletionScalarTower place

instance relativeNormalizedCompletionFinite (place : FinitePlaceAtPrime K p) :
    FiniteDimensional (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
      (CommonPrimeCompletion place) :=
  moduleFinite_completionAlgebra place.val

theorem commonPrimeCompletion_moduleFree (place : FinitePlaceAtPrime K p) :
    Module.Free ℚ_[p] (CommonPrimeCompletion place) := inferInstance

omit [Fact p.Prime] in
theorem commonPrimeCompletion_strongRankCondition (place : FinitePlaceAtPrime K p) :
    StrongRankCondition (CommonPrimeCompletion place) := inferInstance

omit [Fact p.Prime] in
theorem relativeNormalizedCompletion_moduleFree (place : FinitePlaceAtPrime K p) :
    Module.Free (CommonPrimeCompletion (relativeCommonPrimePlace (k := k) place))
      (CommonPrimeCompletion place) := inferInstance

end

end LeanFormal.IUT.NumberFieldFinitePlace
