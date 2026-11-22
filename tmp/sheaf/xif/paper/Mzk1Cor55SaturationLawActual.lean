import tmp.sheaf.xif.paper.Mzk1Section0SaturatedActual

/-!
# Mzk1Cor55SaturationLawActual — derived maximality/intersection laws for saturated
path-pair sets (new theorems; no copies/bookkeeping). No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor55SaturationLawActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual.OrientedGraph
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual

variable {G : OrientedGraph.{0}}

/-- Derived: every saturated set is fixed by intersecting with the co-verticial set. -/
theorem saturated_inter_covert_eq_self (C : PathComposition G)
    (P : Set (PathPairSigma G)) (h : IsSaturatedPathPairSet C P) :
    P ∩ covertSet G = P := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, saturated_subset_covert C P h hx⟩

/-- Derived: the intersection of a saturated set with the co-verticial set is saturated. -/
theorem saturated_inter_covert (C : PathComposition G) (P : Set (PathPairSigma G))
    (h : IsSaturatedPathPairSet C P) : IsSaturatedPathPairSet C (P ∩ covertSet G) := by
  rw [saturated_inter_covert_eq_self C P h]
  exact h

/-- Derived: the co-verticial set is a maximal saturated set. -/
theorem covertSet_maximal (C : PathComposition G) :
    IsSaturatedPathPairSet C (covertSet G) ∧
      ∀ P : Set (PathPairSigma G), IsSaturatedPathPairSet C P → P ⊆ covertSet G :=
  ⟨covertSet_isSaturated C, fun _ h => saturated_subset_covert C _ h⟩

#check saturated_inter_covert_eq_self
#check saturated_inter_covert
#check covertSet_maximal

end LeanFormal.IUT.XiFPaper.Mzk1Cor55SaturationLawActual
end
