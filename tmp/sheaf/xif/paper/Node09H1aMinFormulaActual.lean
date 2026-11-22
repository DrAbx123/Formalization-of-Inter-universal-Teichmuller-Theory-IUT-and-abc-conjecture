import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMinFormulaActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, IsUltrametricDist (E j)]
/-- The H1a min formula: a bounded coordinate ideal is a uniformizer power. -/
theorem coordSubmodule_eq_span_uniformizer_pow
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J)
    [IsDiscreteValuationRing (Integers (E j))]
    (hI : coordSubmodule hna M j ≠ ⊥) :
    ∃ r : Nat, coordSubmodule hna M j =
      Ideal.span {(dvrUniformizer (R := Integers (E j))) ^ r} := by
  letI : IsPrincipalIdealRing (Integers (E j)) := inferInstance
  letI : IsPrincipal (IsLocalRing.maximalIdeal (Integers (E j))) :=
    IsPrincipalIdealRing.principal _
  obtain ⟨r, hr⟩ := exists_maximalIdeal_pow_eq_of_principal
    (R := Integers (E j)) (inferInstance) (coordSubmodule hna M j) hI
  refine ⟨r, ?_⟩
  rw [hr, maximalIdeal_pow_eq_span_uniformizer_pow (R := Integers (E j))]
#check coordSubmodule_eq_span_uniformizer_pow
end LeanFormal.IUT.XiFPaper.Node09H1aMinFormulaActual
end