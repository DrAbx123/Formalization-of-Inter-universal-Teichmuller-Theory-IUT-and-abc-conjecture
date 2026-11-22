import tmp.sheaf.n8.closure.C1P6PrincipalUnitLiftAttempt
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
# C1P6PrincipalUnitSurjectivityCriterion

Exact criterion for principal-unit image surjectivity: it follows from
surjectivity of the actual completion-integers map.  This is the map-level
criterion behind degree-one/unramified cases.

Ramification/index data enter through the production degree decomposition
`relativeCompletionDegree = e * f`; a degree-one (e = 1 and f = 1) situation
is the natural sufficient condition for the map to be a ring equivalence, but
the current production tree does not supply the implication
`relativeCompletionDegree = 1 -> completionIntegersMap surjective`.  That
implication is the exact missing link.  e = 1 alone (unramified with residue
degree > 1) is not asserted sufficient here.

No arbitrary surjectivity is assumed; it is a hypothesis with an actual
criterion and a named missing production link.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6PrincipalUnitSurjectivityCriterion

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.C1P6UnitLiftConditionActual
open LeanFormal.IUT.N8Closure.C1P6PrincipalUnitLiftAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual criterion: surjectivity of the completion-integers map implies
principal-unit image surjectivity. -/
theorem c1P6PrincipalUnitImageSurjective_of_completionIntegersMap_surjective
    (h : Function.Surjective
      (NumberFieldFinitePlace.completionIntegersMap (k := X.S.arithmetic.Fmod)
        (topPlace X))) :
    C1P6PrincipalUnitImageSurjective X := by
  intro v hv
  obtain ⟨x, hx⟩ := h v
  haveI : IsLocalHom (NumberFieldFinitePlace.completionIntegersMap
      (k := X.S.arithmetic.Fmod) (topPlace X)) :=
    NumberFieldFinitePlace.isLocalHom_completionIntegersMap
      (k := X.S.arithmetic.Fmod) (topPlace X)
  have hxunit : IsUnit x :=
    (NumberFieldFinitePlace.isLocalHom_completionIntegersMap
      (k := X.S.arithmetic.Fmod) (topPlace X)).map_nonunit x (hx ▸ v.isUnit)
  refine ⟨hxunit.unit, ?_⟩
  rw [IsUnit.unit_spec hxunit]
  exact hx

/-- The concrete missing degree link: relative completion degree one should
give completion-integers map surjectivity (exact source obligation). -/
def C1P6DegreeOneSurjectivityLink : Prop :=
  NumberFieldFinitePlace.relativeCompletionDegree
      (k := X.S.arithmetic.Fmod) (topPlace X) = 1 →
    Function.Surjective
      (NumberFieldFinitePlace.completionIntegersMap (k := X.S.arithmetic.Fmod)
        (topPlace X))

end LeanFormal.IUT.N8Closure.C1P6PrincipalUnitSurjectivityCriterion