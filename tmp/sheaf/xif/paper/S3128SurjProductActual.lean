import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Ring.Action.Group

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjProductActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- The product decomposition N^n = (h•f)^n * ∏_{g≠1} ((h*g)•f)^n. -/
theorem S3128Surj_prodN (f : A) (n : Nat) (h : G) :
    (h • f) ^ n *
        ((Finset.univ : Finset G).erase 1).prod
          (fun g => ((h * g) • f) ^ n) =
      ((Finset.univ : Finset G).prod (fun x => (x • f) ^ n)) := by
  rw [show (h • f) ^ n = ((h * 1) • f) ^ n by simp]
  conv_lhs =>
    rw [Finset.mul_prod_erase (s := (Finset.univ : Finset G))
      (f := fun g => ((h * g) • f) ^ n) (a := 1) (Finset.mem_univ 1)]
  apply Finset.prod_bij (fun g _ => h * g)
  · intro g _; exact Finset.mem_univ _
  · intro g _ g' _ hg; exact mul_left_cancel hg
  · intro x _; exact ⟨h⁻¹ * x, Finset.mem_univ _, by simp⟩
  · intro g _; rfl

#check S3128Surj_prodN

end LeanFormal.IUT.XiFPaper.S3128SurjProductActual
end