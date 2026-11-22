import Mathlib

/-! Mainline: statement-layer named inputs for H5 hull<=image-volume and H7 Ob9 both-sided
  bounds, with real consumer laws (no fake proofs of the inputs themselves). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1DeepInputStatementsActualAdapted

open LeanFormal.IUT

/-- H5 named input: hull log-volume ≤ image log-volume (O(-)^{-1} normalization shadow). -/
def H5HullImageVolumeInput (hullVolume imageVolume : ℝ) : Prop :=
  hullVolume ≤ imageVolume

theorem h5_hull_le_image_of_input {hullVolume imageVolume : ℝ}
    (h : H5HullImageVolumeInput hullVolume imageVolume) :
    hullVolume ≤ imageVolume :=
  h

/-- H7/Ob9 named input: both-sided bounds at the iterate (lower/upper sandwich data). -/
structure H7Ob9BothSidedInput (lower upper : ℝ) : Prop where
  le_upper : lower ≤ upper

theorem h7_lower_le_upper {lower upper : ℝ}
    (h : H7Ob9BothSidedInput lower upper) : lower ≤ upper :=
  h.le_upper

/-- IUT IV (b)/(c) named-input bundle (height bound and region bound as Props). -/
structure UndilatedBoundsInput (heightBound regionBound : Prop) : Prop where
  height : heightBound
  region : regionBound

theorem undilatedBoundsInput_height {h r : Prop} (H : UndilatedBoundsInput h r) : h :=
  H.height

theorem undilatedBoundsInput_region {h r : Prop} (H : UndilatedBoundsInput h r) : r :=
  H.region

end LeanFormal.IUT.XiFPaper.Mzk1DeepInputStatementsActualAdapted