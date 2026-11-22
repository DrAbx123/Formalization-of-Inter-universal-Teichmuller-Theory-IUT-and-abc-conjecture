import tmp.sheaf.xif.paper.Node09H1aProductFormulaActual
import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMinFormulaDirectFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.XiFPaper.Node09H1aProductFormulaActual

variable {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, IsUltrametricDist (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))

/-- Coordinate projection of a compact integral-ring submodule is compact. -/
theorem coordSubmodule_isCompact (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J)
    (hM : IsCompact (M : Set ((j : J) → E j))) :
    IsCompact (coordSubmodule hna M j : Set (E j)) := by
  have hcont : Continuous (fun x : ((j : J) → E j) => x j) :=
    continuous_apply j
  have h := hM.image hcont
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩

/-- Algebraic part of the H1a minimum formula: if every element of the
coordinate submodule is an integral multiple of a chosen element `x`, then the
coordinate submodule is the principal span of `x`. -/
theorem coordSubmodule_eq_span_of_generator
    (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J) (x : E j)
    (hx : x ∈ coordSubmodule hna M j)
    (hgen : ∀ y ∈ coordSubmodule hna M j, ∃ a : Integers (E j), y = a • x) :
    coordSubmodule hna M j =
      Submodule.span (Integers (E j)) ({x} : Set (E j)) := by
  apply le_antisymm
  · intro y hy
    rcases hgen y hy with ⟨a, rfl⟩
    exact Submodule.smul_mem _ a
      (Submodule.subset_span (Set.mem_singleton x))
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx

#print axioms coordSubmodule_isCompact
#print axioms coordSubmodule_eq_span_of_generator
end LeanFormal.IUT.XiFPaper.Node09H1aMinFormulaDirectFinalActual