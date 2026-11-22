/- Route 8.3 F4 generic finite-exception height lemma: the height bound h_E <= r * h_O(1) + C
may fail only on a finite support; on the support the minimum (of the defect) is absorbed into
the constant, giving a uniform constant C'. -/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F4HeightFiniteActual

/-- Finite-exception height lemma: if hE <= r*hO + C outside a finite set S, then there is a
constant C' with hE <= r*hO + C' everywhere (the support contributes its minimal defect). -/
theorem height_le_mul_add_const_of_finite_exception {α : Type*} [DecidableEq α]
    (hE hO : α → ℝ) (S : Finset α) (r C : ℝ)
    (h_out : ∀ x, x ∉ S → hE x ≤ r * hO x + C) :
    ∃ C' : ℝ, ∀ x, hE x ≤ r * hO x + C' := by
  classical
  by_cases hS : S.Nonempty
  · refine ⟨C + max 0 (S.sup' hS (fun x => hE x - r * hO x - C)), ?_⟩
    intro x
    by_cases hx : x ∈ S
    · have h1 : hE x - r * hO x - C ≤
          S.sup' hS (fun y => hE y - r * hO y - C) :=
        Finset.le_sup' (s := S) (f := fun y => hE y - r * hO y - C) hx
      have h2 : S.sup' hS (fun y => hE y - r * hO y - C) ≤
          max 0 (S.sup' hS (fun y => hE y - r * hO y - C)) := le_max_right _ _
      linarith
    · have h1 := h_out x hx
      have h2 : (0 : ℝ) ≤ max 0 (S.sup' hS (fun y => hE y - r * hO y - C)) := le_max_left _ _
      linarith
  · refine ⟨C, ?_⟩
    intro x
    have hx : x ∉ S := by
      intro hx
      exact hS ⟨x, hx⟩
    exact h_out x hx

/-- The same lemma with the roles named for route F4: h_E <= (r/(n-3)) * h_omega + C outside
the finite support, with the support defect absorbed. -/
theorem hE_le_mul_homega_add_const_of_finite_exception {α : Type*} [DecidableEq α]
    (hE hω : α → ℝ) (S : Finset α) (r : ℝ) (C : ℝ)
    (h_out : ∀ x, x ∉ S → hE x ≤ r * hω x + C) :
    ∃ C' : ℝ, ∀ x, hE x ≤ r * hω x + C' :=
  height_le_mul_add_const_of_finite_exception hE hω S r C h_out

#print axioms height_le_mul_add_const_of_finite_exception
#print axioms hE_le_mul_homega_add_const_of_finite_exception
end LeanFormal.IUT.XiFPaper.Mzk1G1F4HeightFiniteActual
