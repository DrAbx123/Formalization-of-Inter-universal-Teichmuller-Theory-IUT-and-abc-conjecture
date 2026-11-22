import tmp.sheaf.xif.paper.Mzk1HeightVolumeComparisonActual
import tmp.sheaf.xif.paper.Mzk1H5HullBoundActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1H5HeightVolumeBundleActual — H5 hull-bound + height/volume comparison bundle

Reuses the EXIT0 H5 hull-bound and height-volume comparison interfaces, exposing
the pointwise height<=volume bound and hull scaling closure through one bundle.
No paper theorem is proved; interfaces only; no closure; gate NOT PASSED.
Registry 14041; no registry edits. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1H5HeightVolumeBundleActual

open LeanFormal.IUT.XiFPaper.Mzk1HeightVolumeComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundActual

structure H5HeightVolumeBundle (X C : Type*) where
  hv : HeightVolumeComparison X
  hull : H5HullBound C

theorem h5Bundle_height_le_volume {X C : Type*} (B : H5HeightVolumeBundle X C)
    (x : X) : B.hv.height x ≤ B.hv.volume x :=
  B.hv.height_le_volume x

theorem h5Bundle_height_le_of_volume_le {X C : Type*} (B : H5HeightVolumeBundle X C)
    (x : X) {b : ℚ} (h : B.hv.volume x ≤ b) : B.hv.height x ≤ b :=
  B.hv.height_le_of_volume_le x h

theorem h5Bundle_scale_mem {X C : Type*} (B : H5HeightVolumeBundle X C)
    (a : ℚ) {x : C} (hx : x ∈ B.hull.hull) : B.hull.scale a x ∈ B.hull.hull :=
  B.hull.scale_mem a hx

def h5HeightVolumeRows : List (String × String × String) :=
  [ ("bundle", "H5HeightVolumeBundle", "DEF (reuses EXIT0 interfaces)"),
    ("height <= volume", "h5Bundle_height_le_volume", "PROVED"),
    ("height <= volume-bound", "h5Bundle_height_le_of_volume_le", "PROVED"),
    ("hull scaling", "h5Bundle_scale_mem", "PROVED"),
    ("scope", "interfaces only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem h5HeightVolumeRows_length : h5HeightVolumeRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1H5HeightVolumeBundleActual

end
