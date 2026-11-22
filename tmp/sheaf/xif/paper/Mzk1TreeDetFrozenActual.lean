import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: tree-only det tensor fact -> HullDeterminantLogVolumeFrozenSpec (:123) + hullDeterminantLogVolumeFrozenSpec_holds (:153) + hullDeterminantLogVolumeReduction (:636 Obligation) -> PROVED tree-only frozen-spec fact; obligation recorded. No closure.

# Mzk1TreeDetFrozenActual — tree-only det tensor frozen spec

PROVED: the frozen det log-volume spec holds; obligation record fields.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeDetFrozenActual

open LeanFormal.IUT

theorem tree_detFrozenSpec_holds : HullDeterminantLogVolumeFrozenSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

def treeDetRows : List (String × String × String) :=
  [ ("frozen det log-volume spec", "PROVED", "tree_detFrozenSpec_holds (:153)")

  , ("full O(-)^-1 normalization", "NAMED", "no arithmetic-line-bundle API") ]

theorem treeDetRows_length : treeDetRows.length = 2 := rfl

#check tree_detFrozenSpec_holds
#check treeDetRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeDetFrozenActual
end