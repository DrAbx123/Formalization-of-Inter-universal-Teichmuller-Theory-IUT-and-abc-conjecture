import tmp.sheaf.n8.closure.C1P6QUniformizerNormalization
import tmp.sheaf.n8.closure.C1P6RamificationTransportCondition

/-!
# C1P6RangeConditionCriterion

Exact criterion for the range condition using the actual q = π^n * unit
normalization.  If the chosen uniformizer π is itself in the completion-map
unit image, then the range condition is equivalent to the normalized unit
being in the completion-map unit image.

Residue comparison (Wave28/30) is necessary for that unit lift, but residue
comparison alone is not sufficient: it does not supply the actual unit lift.
Thus the exact criterion separates the actual unit-lift condition from the
decidable residue shadow; no arbitrary lift is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6RangeConditionCriterion

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6RamificationTransportCondition
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The normalized unit is in the completion-map unit image. -/
def C1P6UnitLiftCondition : Prop :=
  ∃ u : (NumberFieldFinitePlace.Completion (basePlace X))ˣ,
    NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.Fmod) (topPlace X)
      (u : NumberFieldFinitePlace.Completion (basePlace X)) =
      ((c1P6QUniformizerNormalization X).unit :
        NumberFieldFinitePlace.Completion (topPlace X))

/-- The chosen uniformizer lies in the completion-map unit image. -/
def C1P6UniformizerLiftCondition : Prop :=
  ∃ πb : (NumberFieldFinitePlace.Completion (basePlace X))ˣ,
    NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.Fmod) (topPlace X)
      (πb : NumberFieldFinitePlace.Completion (basePlace X)) =
      ((c1P6QUniformizerNormalization X).uniformizer :
        NumberFieldFinitePlace.Completion (topPlace X))

/-- Sufficiency: a uniformizer lift plus a unit lift gives the range condition. -/
theorem c1P6RangeCondition_of_unitLift
    (hπ : C1P6UniformizerLiftCondition X)
    (hu : C1P6UnitLiftCondition X) :
    C1P6RangeCondition X := by
  rcases hπ with ⟨πb, hπ⟩
  rcases hu with ⟨u, hu⟩
  refine ⟨u * πb ^ (c1P6QUniformizerNormalization X).exponent, ?_⟩
  change NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.Fmod) (topPlace X)
    (((u * πb ^ (c1P6QUniformizerNormalization X).exponent :
      (NumberFieldFinitePlace.Completion (basePlace X))ˣ) :
      NumberFieldFinitePlace.Completion (basePlace X))) =
    (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X))
  rw [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hu, hπ]
  exact (c1P6QUniformizerNormalization X).q_eq.symm

end LeanFormal.IUT.N8Closure.C1P6RangeConditionCriterion