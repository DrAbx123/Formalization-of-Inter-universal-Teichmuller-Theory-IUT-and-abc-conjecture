import tmp.sheaf.xif.paper.Node09H1aProductFormulaActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1GenericDVRDecompositionActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Node09H1aProductFormulaActual

variable {p : Nat} [Fact p.Prime] {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, CharZero (E j)]
variable [∀ j, IsUltrametricDist (E j)] [∀ j, CompleteSpace (E j)] [∀ j, ProperSpace (E j)]
variable [∀ j, NormedAlgebra (Padic p) (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))

/-- Every ideal of a principal ideal ring is a principal span. -/
theorem ideal_eq_span_singleton {R : Type*} [CommRing R] [IsPrincipalIdealRing R]
    (I : Ideal R) : ∃ a : R, I = Ideal.span {a} := by
  obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal I
  exact ⟨a, ha⟩

#print axioms ideal_eq_span_singleton

/-- Generic idempotent coordinate decomposition of an integral-ring
submodule of a finite product. -/
theorem submodule_eq_pi_coord_generic
    (M : Submodule (integralRing hna) ((j : J) → E j)) :
    (M : Set ((j : J) → E j)) =
      Set.pi Set.univ (fun j => (coordSubmodule hna M j : Set (E j))) :=
  submodule_eq_pi_coord hna M

#print axioms submodule_eq_pi_coord_generic

end LeanFormal.IUT.XiFPaper.Node09H1GenericDVRDecompositionActual