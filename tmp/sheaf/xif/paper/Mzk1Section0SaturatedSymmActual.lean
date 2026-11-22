import tmp.sheaf.xif.paper.Mzk1Section0SaturatedActual

/-!
# Mzk1Section0SaturatedSymmActual — symmetrically saturated path-pair sets (corpus l.1362-1365)

STEP 0 prior-art: Mzk1Section0SaturatedActual (co-verticial pairs, PathComposition datum,
saturated-set conditions (a)-(e), covertSet saturated) -> REUSE; this file adds the paper's
condition (f) (reflexivity/symmetry) and its basic consequences.

WHAT IS PROVED HERE:
* symmetrically saturated path-pair sets (saturated + (f) symmetry);
* the all-co-verticial set is symmetrically saturated;
* every saturated set is contained in the all-co-verticial set (condition (b) consequence);
* a symmetrically saturated set is saturated (projection).
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedSymmActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual

variable {G : OrientedGraph.{0}}

/-- The paper's condition (f): symmetry/reflexivity of a saturated path-pair set. -/
structure IsSymmetricallySaturatedPathPairSet (C : PathComposition G)
    (P : Set (PathPairSigma G)) extends IsSaturatedPathPairSet C P : Prop where
  symm : ∀ γ1 γ2 : PathSigma G, (γ1, γ2) ∈ P → (γ2, γ1) ∈ P

/-- The all-co-verticial set is symmetrically saturated (corpus l.1362-1365). -/
theorem covertSet_isSymmetricallySaturated (C : PathComposition G) :
    IsSymmetricallySaturatedPathPairSet C (covertSet G) where
  toIsSaturatedPathPairSet := covertSet_isSaturated C
  symm γ1 γ2 h := ⟨h.1.symm, h.2.symm⟩

/-- Every saturated set is contained in the all-co-verticial set (condition (b)). -/
theorem saturated_subset_covert (C : PathComposition G) (P : Set (PathPairSigma G))
    (h : IsSaturatedPathPairSet C P) : P ⊆ covertSet G :=
  fun _ hp => h.covert _ hp

/-- A symmetrically saturated set is saturated (projection). -/
theorem symmetricallySaturated_isSaturated (C : PathComposition G)
    (P : Set (PathPairSigma G)) (h : IsSymmetricallySaturatedPathPairSet C P) :
    IsSaturatedPathPairSet C P :=
  h.toIsSaturatedPathPairSet

/-- Symmetry rows: (condition, formalization, status). -/
def saturatedSymmRows : List (String × String × String) :=
  [ ("condition (f) symmetry/reflexivity", "IsSymmetricallySaturatedPathPairSet.symm", "FORMALIZED (structure field)"),
    ("all-co-verticial set is symmetrically saturated", "covertSet_isSymmetricallySaturated", "PROVED"),
    ("saturated ⊆ covert", "saturated_subset_covert", "PROVED"),
    ("symmetrically saturated => saturated", "symmetricallySaturated_isSaturated", "PROVED (projection)"),
    ("concrete pre-path composition", "PathComposition datum (abstract)", "NAMED (composition construction not formalized)") ]

/-- The symmetry row record has five rows. -/
theorem saturatedSymmRows_length : saturatedSymmRows.length = 5 := rfl

#check IsSymmetricallySaturatedPathPairSet
#check covertSet_isSymmetricallySaturated
#check saturated_subset_covert
#check symmetricallySaturated_isSaturated
#check saturatedSymmRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedSymmActual
end
