import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetMemActual — membership lemmas for the finite step set (real)

Real Lean (no sorry/axiom): the three ways a point lies in the paper's step set (image of S,
image of a conjugate, image of a critical point).  Registry frozen 14041. -/

open Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMemActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem mem_stepSet_of_mem (S : Finset Qbar) (alpha0 x : Qbar) (hx : x ∈ S) :
    aeval x (minpoly ℚ alpha0) ∈ stepSet S alpha0 := by
  unfold stepSet
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨x, Finset.mem_union_left _ hx, rfl⟩

theorem mem_stepSet_of_mem_conj (S : Finset Qbar) (alpha0 x : Qbar)
    (hx : x ∈ conjSet alpha0) :
    aeval x (minpoly ℚ alpha0) ∈ stepSet S alpha0 := by
  unfold stepSet
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨x, Finset.mem_union_right _ hx, rfl⟩

theorem mem_stepSet_of_mem_crit (S : Finset Qbar) (alpha0 x : Qbar)
    (hx : x ∈ critSet alpha0) :
    aeval x (minpoly ℚ alpha0) ∈ stepSet S alpha0 := by
  unfold stepSet
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

def finiteStepSetMemRows : List (String × String) :=
  [ ("mem_stepSet_of_mem", "PROVED"), ("mem_stepSet_of_mem_conj", "PROVED"),
    ("mem_stepSet_of_mem_crit", "PROVED") ]

theorem finiteStepSetMemRows_length : finiteStepSetMemRows.length = 3 := rfl

theorem image_subset_stepSet (S : Finset Qbar) (alpha0 : Qbar) :
    S.image (fun x => aeval x (minpoly ℚ alpha0)) ⊆ stepSet S alpha0 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact mem_stepSet_of_mem S alpha0 x hx

theorem conjImage_subset_stepSet (S : Finset Qbar) (alpha0 : Qbar) :
    (conjSet alpha0).image (fun x => aeval x (minpoly ℚ alpha0)) ⊆ stepSet S alpha0 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact mem_stepSet_of_mem_conj S alpha0 x hx

theorem critImage_subset_stepSet (S : Finset Qbar) (alpha0 : Qbar) :
    (critSet alpha0).image (fun x => aeval x (minpoly ℚ alpha0)) ⊆ stepSet S alpha0 := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  exact mem_stepSet_of_mem_crit S alpha0 x hx

#check image_subset_stepSet

#check mem_stepSet_of_mem

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMemActual
end
