import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: H5 tree-asset bundle -> SourceHullCompactnessReduction (IQHullLogVolumeInterface; imageSet_logVolume_le_hull:88, hull_logVolume_lt_top:95, lower_bound_and_finiteness:104) + HullDeterminantLogVolumeReduction (HullDeterminantLogVolumeFrozenSpec:123, hullDeterminantLogVolumeFrozenSpec_holds:153, packetLogVolume_eq_matrixLogDet:249) -> PROVED tree-asset bundle consumed by paper hull rows. No new math; no closure.

# Mzk1TreeHullBundleActual — H5 tree-asset bundle

PROVED:
* `treeHull_interface_bundle`: imageSet<=hull + finite hull volume + frozen det spec;
* `treeHull_lower_bound`: lower-bound propagation.
CONSUMED TREE ASSETS: IQHullLogVolumeInterface, HullDeterminantLogVolumeFrozenSpec.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeHullBundleActual

open LeanFormal.IUT

universe u

/-- **PROVED:** H5 tree-asset bundle. -/
theorem treeHull_interface_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧
      HullDeterminantLogVolumeFrozenSpec :=
  ⟨W.imageSet_subset_hull, W.hull_logVolume_lt_top,
    hullDeterminantLogVolumeFrozenSpec_holds⟩

/-- **PROVED:** lower-bound propagation for the hull volume. -/
theorem treeHull_lower_bound {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull :=
  le_trans h W.imageSet_logVolume_le_hull

def treeHullRows : List (String × String × String) :=
  [ ("IQ hull interface bundle", "PROVED", "treeHull_interface_bundle")
  , ("hull lower-bound propagation", "PROVED", "treeHull_lower_bound")
  , ("frozen det log-volume spec", "PROVED (tree)", "hullDeterminantLogVolumeFrozenSpec_holds (:153)")
  , ("H5 named O(-)^-1 normalization / hull<=image-volume", "NAMED", "Hull09 rows; not formalized") ]

theorem treeHullRows_length : treeHullRows.length = 4 := rfl

#check treeHull_interface_bundle
#check treeHull_lower_bound
#check treeHullRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeHullBundleActual
end