import tmp.sheaf.xif.paper.Mzk1Section0OrderLawsActual
import tmp.sheaf.xif.paper.Mzk1Section0SaturatedSymmActual
import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainSection0Actual — chained Section-0 laws consumers

Chains EXIT0 Section-0 assets: ordered-set laws, symmetric saturation and graph
reachability.  No new math; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainSection0Actual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0OrderLawsActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedSymmActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0GraphActual

universe u

theorem chain_countablyOrdered_iff (E : Type u) [Preorder E] :
    CountablyOrdered E ↔
      ∃ E' : Set ℤ, OrderwiseConnected E' ∧ Nonempty (E ≃o ↥E') :=
  countablyOrdered_iff E

theorem chain_orderwiseConnected_Icc (a b : ℤ) :
    OrderwiseConnected (Set.Icc a b) :=
  orderwiseConnected_Icc a b

theorem chain_symmSaturated_isSaturated {G : OrientedGraph.{u}} (C : PathComposition G)
    (P : Set (PathPairSigma G)) (h : IsSymmetricallySaturatedPathPairSet C P) :
    IsSaturatedPathPairSet C P :=
  symmetricallySaturated_isSaturated C P h

theorem chain_saturated_subset_covert {G : OrientedGraph.{u}} (C : PathComposition G)
    (P : Set (PathPairSigma G)) (h : IsSaturatedPathPairSet C P) : P ⊆ covertSet G :=
  saturated_subset_covert C P h

theorem chain_reach_le {n m : ℤ} (h : Reach n m) : n ≤ m := reach_le h

def chainSection0Rows : List (String × String × String) :=
  [ ("countably ordered", "chain_countablyOrdered_iff", "PROVED (reuse)"),
    ("orderwise connected Icc", "chain_orderwiseConnected_Icc", "PROVED (reuse)"),
    ("symmetric saturation", "chain_symmSaturated_isSaturated", "PROVED (reuse)"),
    ("saturated subset covert", "chain_saturated_subset_covert", "PROVED (reuse)"),
    ("reachability", "chain_reach_le", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem chainSection0Rows_length : chainSection0Rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainSection0Actual

end
