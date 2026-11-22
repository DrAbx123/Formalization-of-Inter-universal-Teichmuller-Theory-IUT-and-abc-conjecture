import tmp.sheaf.n8.closure.C1P6UnitLiftConditionActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# C1P6PrincipalUnitLiftAttempt

Attempt to close the principal-unit part of the normalized unit lift using the
principal-unit filtration `1 + maximalIdeal`.

Production has no theorem that the principal units of the top completion are
in the image of the base principal units.  The only production principal-unit
transport in the tree is the special degree-one/unramified Q5 comparison
`concretePlace_principalUnitsEquiv`; it does not apply to an arbitrary native
input X.  Therefore the exact missing production declaration is recorded
below: principal-unit image surjectivity.

The residue part is already decidable (Wave30) and is only a lift modulo the
maximal ideal; it does not produce the actual principal-unit lift.  No
arbitrary lift is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6PrincipalUnitLiftAttempt

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.C1P6RangeConditionCriterion
open LeanFormal.IUT.N8Closure.C1P6UnitLiftConditionActual
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact missing production declaration: every principal unit of the top
completion integers is induced by a base completion-integer unit.

This is the principal-unit filtration statement needed to close the lift.  It
is not provided by the current production tree; the Q5 special case is
degree-one only. -/
def C1P6PrincipalUnitImageSurjective : Prop :=
  ∀ v : (TopIntegers X)ˣ,
    IsLocalRing.residue (TopIntegers X) v = 1 →
    ∃ u : ((basePlace X).maximalIdeal.adicCompletionIntegers
        X.S.arithmetic.Fmod)ˣ,
      NumberFieldFinitePlace.completionIntegersMap (k := X.S.arithmetic.Fmod)
        (topPlace X) (u : (basePlace X).maximalIdeal.adicCompletionIntegers
          X.S.arithmetic.Fmod) = v

/-- The actual integral lift remains the strongest available sufficient
condition (from Wave32). -/
theorem c1P6UnitLiftCondition_of_integral_reexport
    (h : C1P6IntegralUnitLiftCondition X) :
    C1P6UnitLiftCondition X :=
  c1P6UnitLiftCondition_of_integral X h

end LeanFormal.IUT.N8Closure.C1P6PrincipalUnitLiftAttempt