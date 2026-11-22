import tmp.sheaf.n8.closure.C1P6RangeConditionCriterion
import tmp.sheaf.n8.closure.C1P6UnitResidueComparison
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
# C1P6UnitLiftConditionActual

Attempt at the actual normalized unit lift.  The strongest actual statement
available is the integral unit lift: a base completion-integer unit whose
`completionIntegersMap` is the normalized unit of the top completion integers.

It implies the unit residue comparison (`residueMap_residue`).  Converse does
not follow from Hensel/finite residue data: a residue comparison lifts a unit
only modulo the maximal ideal; the remaining quotient is a principal unit,
and no production principal-unit comparison exists.  This is the exact
missing source object; no arbitrary lift is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6UnitLiftConditionActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.C1P6RangeConditionCriterion
open LeanFormal.IUT.N8Closure.C1P6UnitResidueComparison
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Stronger actual target: an integral base unit mapping to the normalized
top unit under the actual completion-integers map. -/
def C1P6IntegralUnitLiftCondition : Prop :=
  ∃ u : ((basePlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.Fmod)ˣ,
    NumberFieldFinitePlace.completionIntegersMap (k := X.S.arithmetic.Fmod)
      (topPlace X) (u : (basePlace X).maximalIdeal.adicCompletionIntegers
        X.S.arithmetic.Fmod) =
      ((normData X).unit : TopIntegers X)

/-- Integral unit lift implies the completion-unit lift. -/
theorem c1P6UnitLiftCondition_of_integral
    (h : C1P6IntegralUnitLiftCondition X) :
    C1P6UnitLiftCondition X := by
  rcases h with ⟨u, hu⟩
  have hne : ((u : (basePlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.Fmod) :
      NumberFieldFinitePlace.Completion (basePlace X)) ≠ 0 := by
    intro hzero
    exact Units.ne_zero u (Subtype.ext hzero)
  refine ⟨Units.mk0 ((u : (basePlace X).maximalIdeal.adicCompletionIntegers
    X.S.arithmetic.Fmod) : NumberFieldFinitePlace.Completion (basePlace X)) hne, ?_⟩
  have hcoe := congrArg (fun y : TopIntegers X =>
    (y : NumberFieldFinitePlace.Completion (topPlace X))) hu
  simpa [normData, NumberFieldFinitePlace.coe_completionIntegersMap] using hcoe

/-- Integral unit lift implies the actual unit residue comparison, using the
production `residueMap_residue`. -/
theorem c1P6UnitResidueComparison_of_integral
    (h : C1P6IntegralUnitLiftCondition X) :
    C1P6UnitResidueComparison X := by
  rcases h with ⟨u, hu⟩
  refine ⟨IsLocalRing.residue
    ((basePlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.Fmod)
    (u : (basePlace X).maximalIdeal.adicCompletionIntegers
      X.S.arithmetic.Fmod), ?_⟩
  rw [NumberFieldFinitePlace.residueMap_residue]
  rw [hu]
  rfl

end LeanFormal.IUT.N8Closure.C1P6UnitLiftConditionActual