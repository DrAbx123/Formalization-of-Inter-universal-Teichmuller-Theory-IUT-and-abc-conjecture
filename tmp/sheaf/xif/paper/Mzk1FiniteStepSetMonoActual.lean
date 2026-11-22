import tmp.sheaf.xif.paper.Mzk1NestedInductionActual

/-! # Mzk1FiniteStepSetMonoActual — monotonicity of the finite step set (real)

Real Lean (no sorry/axiom): the paper's step-set operator is monotone in the point set.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMonoActual

open LeanFormal.IUT.XiFPaper.Mzk1NestedInductionActual

attribute [local instance] Classical.decEq

universe u

theorem stepSet_mono (S T : Finset Qbar) (alpha0 : Qbar) (h : S ⊆ T) :
    stepSet S alpha0 ⊆ stepSet T alpha0 := by
  unfold stepSet
  apply Finset.union_subset_union
  · apply Finset.image_subset_image
    exact Finset.union_subset_union h (Finset.Subset.refl _)
  · exact Finset.Subset.refl _

theorem maxDeg_stepSet_mono {S T : Finset Qbar} (alpha0 : Qbar) (h : S ⊆ T) :
    maxDeg (stepSet S alpha0) <= maxDeg (stepSet T alpha0) := by
  unfold maxDeg
  exact Finset.sup_mono (stepSet_mono S T alpha0 h)

def finiteStepSetMonoRows : List (String × String) :=
  [ ("stepSet_mono", "PROVED"), ("maxDeg_stepSet_mono", "PROVED") ]

theorem finiteStepSetMonoRows_length : finiteStepSetMonoRows.length = 2 := rfl

#check stepSet_mono

end LeanFormal.IUT.XiFPaper.Mzk1FiniteStepSetMonoActual
end
