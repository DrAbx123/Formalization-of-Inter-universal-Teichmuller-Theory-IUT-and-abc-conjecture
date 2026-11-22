import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMaxNormPrincipalActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
open scoped Pointwise BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, IsUltrametricDist (E j)]
/-- A submodule of K over its valuation ring that contains 1 and lies in the
valuation ring is the whole valuation ring. -/
theorem submodule_eq_span_one_of_one_mem {K : Type*} [NormedField K]
    [IsUltrametricDist K] (I : Submodule (Integers K) K)
    (h1 : (1 : K) ∈ I) (hO : ∀ y ∈ I, y ∈ Integers K) :
    I = Submodule.span (Integers K) {(1 : K)} := by
  apply le_antisymm
  · intro y hy
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨y, hO y hy⟩, ?_⟩
    simp [Subring.smul_def]
  · intro y hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    exact I.smul_mem a h1
/-- H1a max-norm/one-membership specialization for the coordinate projection. -/
theorem coordSubmodule_eq_span_one
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J)
    (h1 : (1 : E j) ∈ coordSubmodule hna M j)
    (hO : ∀ y ∈ coordSubmodule hna M j, y ∈ Integers (E j)) :
    coordSubmodule hna M j =
      Submodule.span (Integers (E j)) {(1 : E j)} :=
  submodule_eq_span_one_of_one_mem (coordSubmodule hna M j) h1 hO
#check submodule_eq_span_one_of_one_mem
#check coordSubmodule_eq_span_one
end LeanFormal.IUT.XiFPaper.Node09H1aMaxNormPrincipalActual
end