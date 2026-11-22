import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: tree-only IQ hull facts -> IQHullLogVolumeInterface (SourceHullCompactnessReduction:52) -> PROVED tree-only facts bundle (no dependency on our paper files). No closure.

# Mzk1TreeIQHullFactsActual — tree-only IQ hull facts

PROVED: image subset hull; finite hull volume; scale-shift monotonicity; lower-bound propagation; bundle.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual

open LeanFormal.IUT

universe u

theorem tree_iqHull_image_subset {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull := W.imageSet_subset_hull

theorem tree_iqHull_finite {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull < ⊤ := W.hull_logVolume_lt_top

theorem tree_iqHull_scaleShift_le {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume (W.scaleShift '' W.unitRegion) ≤ W.logVolume W.unitRegion :=
  W.scaleShift_unitRegion_logVolume_le

theorem tree_iqHull_lower_bound {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull :=
  le_trans h W.imageSet_logVolume_le_hull

theorem tree_iqHull_bundle {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    W.imageSet ⊆ W.hull ∧ lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨W.imageSet_subset_hull, le_trans h W.imageSet_logVolume_le_hull, W.hull_logVolume_lt_top⟩

def treeIQHullRows : List (String × String × String) :=
  [ ("image subset hull", "PROVED", "tree_iqHull_image_subset")
  , ("finite hull volume", "PROVED", "tree_iqHull_finite")
  , ("scale-shift monotonicity", "PROVED", "tree_iqHull_scaleShift_le")
  , ("lower-bound propagation", "PROVED", "tree_iqHull_lower_bound")
  , ("bundled conclusions", "PROVED", "tree_iqHull_bundle") ]

theorem treeIQHullRows_length : treeIQHullRows.length = 5 := rfl

#check tree_iqHull_bundle
#check tree_iqHull_lower_bound
#check treeIQHullRows_length

end LeanFormal.IUT.XiFPaper.Mzk1TreeIQHullFactsActual
end