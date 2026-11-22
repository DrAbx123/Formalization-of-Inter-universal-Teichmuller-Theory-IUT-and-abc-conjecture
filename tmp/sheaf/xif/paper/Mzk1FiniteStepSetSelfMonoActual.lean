import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetSelfMonoActual — self-contained monotonicity of iterated step sets

Real Lean (no sorry/axiom): the paper's step-set operator is monotone, hence its iterates and
their maximal degrees are monotone in the initial set.  Only green dependencies.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetSelfMonoActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem stepSet_mono' (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) :
    stepSet S alpha0 ⊆ stepSet T alpha0 := by
  unfold stepSet
  apply Finset.union_subset_union
  · apply Finset.image_subset_image
    exact Finset.union_subset_union h (Finset.Subset.refl _)
  · exact Finset.Subset.refl _

theorem iterate_subset' (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) (n : Nat) :
    Nat.iterate (fun X => stepSet X alpha0) n S ⊆
      Nat.iterate (fun X => stepSet X alpha0) n T := by
  induction n with
  | zero => exact h
  | succ n ih =>
      exact stepSet_mono' _ _ alpha0 ih

theorem maxDeg_iterate_mono (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) (n : Nat) :
    maxDeg (Nat.iterate (fun X => stepSet X alpha0) n S) <=
      maxDeg (Nat.iterate (fun X => stepSet X alpha0) n T) := by
  unfold maxDeg
  exact Finset.sup_mono (iterate_subset' S T alpha0 h n)

def finiteStepSetSelfMonoRows : List (String × String) :=
  [ ("stepSet_mono'", "PROVED"), ("iterate_subset'", "PROVED"),
    ("maxDeg_iterate_mono", "PROVED") ]

theorem finiteStepSetSelfMonoRows_length : finiteStepSetSelfMonoRows.length = 3 := rfl

theorem card_iterate_mono (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) (n : Nat) :
    (Nat.iterate (fun X => stepSet X alpha0) n S).card
      <= (Nat.iterate (fun X => stepSet X alpha0) n T).card :=
  Finset.card_le_card (iterate_subset' S T alpha0 h n)

theorem card_stepSet_le_of_subset (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) :
    (stepSet S alpha0).card <= (stepSet T alpha0).card :=
  Finset.card_le_card (stepSet_mono' S T alpha0 h)

#check card_iterate_mono

#check maxDeg_iterate_mono

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetSelfMonoActual
end
