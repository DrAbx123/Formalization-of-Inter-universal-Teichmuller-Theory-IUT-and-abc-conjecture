import tmp.sheaf.xif.paper.Mzk1Section0SaturatedSymmActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1Section0SymmClosureConsumerActual — symmetric saturation consumers

Reuses the EXIT0 symmetric-saturation laws: symmetric saturation implies ordinary
saturation, and saturated sets lie in the covert set.  No new math; no closure;
gate NOT PASSED; registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0SymmClosureConsumerActual

open LeanFormal.IUT.XiFPaper.AbsTopIII05Section0ObjectsActual
open LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedSymmActual

universe u

variable {G : OrientedGraph.{u}}

theorem symmSaturated_isSaturated_consumer (C : PathComposition G)
    (P : Set (PathPairSigma G))
    (h : IsSymmetricallySaturatedPathPairSet C P) :
    LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual.IsSaturatedPathPairSet C P :=
  symmetricallySaturated_isSaturated C P h

theorem saturated_subset_covert_consumer (C : PathComposition G)
    (P : Set (PathPairSigma G))
    (h : LeanFormal.IUT.XiFPaper.Mzk1Section0SaturatedActual.IsSaturatedPathPairSet C P) :
    P ⊆ covertSet G :=
  saturated_subset_covert C P h

def section0SymmConsumerRows : List (String × String × String) :=
  [ ("symmetric -> saturated", "symmSaturated_isSaturated_consumer", "PROVED (reuse)"),
    ("saturated -> covert", "saturated_subset_covert_consumer", "PROVED (reuse)"),
    ("scope", "no new math; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem section0SymmConsumerRows_length : section0SymmConsumerRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Section0SymmClosureConsumerActual

end
