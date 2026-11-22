/- Generic product-ring coordinate decomposition: a submodule over a product
ring is the product of its coordinate projections.  Independent file. -/
import Mathlib

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aCoordinateProjectionActual
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {O : J → Type*} [∀ j, CommRing (O j)]
variable {E : J → Type*} [∀ j, AddCommGroup (E j)] [∀ j, Module (O j) (E j)]

/-- A submodule over a product ring is the product of its coordinate projections. -/
theorem submodule_eq_pi_projections
    (M : Submodule ((j : J) → O j) ((j : J) → E j)) :
    (M : Set ((j : J) → E j)) =
      Set.pi Set.univ (fun j => {x j | x ∈ M}) := by
  ext x
  constructor
  · intro hx j _
    exact ⟨x, hx, rfl⟩
  · intro hx
    have hx' : ∀ j, ∃ z : (j : J) → E j, z ∈ M ∧ z j = x j :=
      fun j => hx j (Set.mem_univ j)
    choose y hy using hx'
    let s : J → ((j : J) → E j) :=
      fun j => (Pi.single j (1 : O j) : (j : J) → O j) • y j
    have hmem : ∀ j, s j ∈ M := fun j => M.smul_mem _ (hy j).1
    have hsum : (∑ j, s j) ∈ M :=
      Submodule.sum_mem M (fun j _ => hmem j)
    have hx_eq : x = ∑ j, s j := by
      funext k
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single k]
      · dsimp [s]
        rw [Pi.single_eq_same]
        rw [one_smul]
        exact (hy k).2.symm
      · intro j _ hjk
        dsimp [s]
        have hkj : k ≠ j := fun h => hjk h.symm
        rw [Pi.single_eq_of_ne hkj]
        rw [zero_smul]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    rw [hx_eq]
    exact hsum

#check submodule_eq_pi_projections
end LeanFormal.IUT.XiFPaper.Node09H1aCoordinateProjectionActual
end
