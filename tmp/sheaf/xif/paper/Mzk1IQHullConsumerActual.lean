import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: iutiv-abc:IQHull (interface node) -> tree IQHullLogVolumeInterface (SourceHullCompactnessReduction.lean:52) + imageSet_logVolume_le_hull:88 / hull_logVolume_lt_top:95 / lower_bound_and_finiteness:104 + ValueHullCompactnessInput (SourceHullInterfaceDischarge.lean:205) -> paper-layer consumer bundle: typed interface consumption, finite hull log-volume, lower-bound propagation; named compactness input recorded. No new math; no closure.

# Mzk1IQHullConsumerActual — H5/IQ hull interface consumer (paper layer)

PROVED:
* `iqHull_imageSet_le`: image-union log-volume <= hull log-volume;
* `iqHull_finite`: hull log-volume is finite;
* `iqHull_lower_bound`: any lower bound of the image-union volume propagates;
* `iqHull_bundle`: the paper's two conclusions bundled from one interface.
NAMED: the interface data itself (IQHullLogVolumeInterface = paper ambient carrier data)
and the value-level compactness input (ValueHullCompactnessInput in the tree discharge).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT

universe u

/-- **PROVED:** image-union log-volume is a lower bound for the hull log-volume. -/
theorem iqHull_imageSet_le {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.imageSet ≤ W.logVolume W.hull :=
  W.imageSet_logVolume_le_hull

/-- **PROVED:** the hull log-volume is finite (conditional on the interface). -/
theorem iqHull_finite {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull < ⊤ :=
  W.hull_logVolume_lt_top

/-- **PROVED:** a lower bound on the image-union volume propagates to the hull. -/
theorem iqHull_lower_bound {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull :=
  le_trans h W.imageSet_logVolume_le_hull

/-- **PROVED (bundled):** the paper's two conclusions from one interface. -/
theorem iqHull_bundle {X : Type u} (W : IQHullLogVolumeInterface X)
    {lowerBound : ENNReal} (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  W.lower_bound_and_finiteness h

end LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.Mzk1IQHullConsumerActual

/-- Rows: proved consumer vs named interface data. -/
def iqHullConsumerRows : List (String × String × String) :=
  [ ("image-union volume <= hull volume", "PROVED", "LeanFormal.IUT.iqHull_imageSet_le (tree SourceHullCompactnessReduction:88)")
  , ("hull log-volume finite", "PROVED", "LeanFormal.IUT.iqHull_finite (:95)")
  , ("lower-bound propagation", "PROVED", "LeanFormal.IUT.iqHull_lower_bound")
  , ("bundled paper conclusions", "PROVED", "LeanFormal.IUT.iqHull_bundle (:104)")
  , ("IQHullLogVolumeInterface data", "NAMED interface", "paper ambient carrier data (SourceHullCompactnessReduction:52); no field follows from OriginalInput")
  , ("value-level compactness input", "NAMED (tree)", "ValueHullCompactnessInput / sourceHullVolume_lt_top_of_compactnessInput (SourceHullInterfaceDischarge:205/223)") ]

theorem iqHullConsumerRows_length : iqHullConsumerRows.length = 6 := rfl

#check LeanFormal.IUT.iqHull_imageSet_le
#check LeanFormal.IUT.iqHull_finite
#check LeanFormal.IUT.iqHull_bundle
#check iqHullConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IQHullConsumerActual
end