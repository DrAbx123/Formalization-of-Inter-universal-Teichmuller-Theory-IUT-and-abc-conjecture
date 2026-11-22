import tmp.sheaf.xif.paper.Mzk1IQHullConsumerActual
import tmp.sheaf.xif.paper.Mzk1IQHullMonotonicityActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # IQ hull green consumer bundle; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IQHullGreenConsumerActualAdapted

open LeanFormal.IUT

universe u

theorem iqHullGreen_bundle {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.imageSet ⊆ W.hull ∧ W.logVolume W.hull < ⊤ ∧
      W.logVolume (W.scaleShift '' W.unitRegion) ≤ W.logVolume W.unitRegion :=
  ⟨LeanFormal.IUT.iqHull_image_subset W,
    (LeanFormal.IUT.iqHull_finite_and_lower W le_rfl).2,
    LeanFormal.IUT.iqHull_scaleShift_mono W⟩

def iqHullGreenRows : List (String × String × String) :=
  [ ("image/finite/scale-shift bundle", "PROVED", "iqHullGreen_bundle") ]

theorem iqHullGreenRows_length : iqHullGreenRows.length = 1 := rfl

#check iqHullGreen_bundle
#check iqHullGreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IQHullGreenConsumerActualAdapted
end