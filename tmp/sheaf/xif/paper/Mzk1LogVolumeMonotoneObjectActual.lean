/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual

/-!
# Mzk1LogVolumeMonotoneObjectActual — log-volume monotonicity object (xi-e step)

A524: the monotonicity object used by the xi-e⇒xi-f step: a hull with its
actual image contained in it and a normalized Haar log-volume, together with
the monotonicity of the log-volume (`s1902LogVolume_mono`).  Hence the log-volume
of the actual Theta image is at most the log-volume of its holomorphic hull.

Reuses the green S1902 root-extension hull/Haar assets; no new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeMonotoneObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The log-volume monotonicity object: image, hull and normalized Haar log-volume. -/
structure HullLogVolumeMonotoneObject where
  /-- the actual Theta image. -/
  imageSet : Set (S1902Carrier T)
  /-- its holomorphic hull. -/
  hull : Set (S1902Carrier T)
  /-- the normalized Haar log-volume. -/
  logVolume : Set (S1902Carrier T) → ENNReal

/-- The constructed object from the green S1902 assets. -/
noncomputable def hullLogVolumeMonotoneObject : HullLogVolumeMonotoneObject T where
  imageSet := s1902ImageSet T
  hull := s1902Hull T
  logVolume := s1902LogVolume T

/-- `_constructed`: the image is the actual S1902 Theta image. -/
theorem hullLogVolumeMonotoneObject_image :
    (hullLogVolumeMonotoneObject T).imageSet = s1902ImageSet T := rfl

/-- The image is contained in the hull. -/
theorem hullLogVolumeMonotoneObject_image_subset :
    (hullLogVolumeMonotoneObject T).imageSet ⊆ (hullLogVolumeMonotoneObject T).hull :=
  s1902ImageSet_subset_hull T

/-- Log-volume is monotone under inclusion. -/
theorem hullLogVolumeMonotoneObject_logVolume_mono
    {S U : Set (S1902Carrier T)} (hSU : S ⊆ U) :
    (hullLogVolumeMonotoneObject T).logVolume S ≤
      (hullLogVolumeMonotoneObject T).logVolume U :=
  s1902LogVolume_mono T hSU

/-- The image log-volume is at most the hull log-volume (xi-e monotonicity step). -/
theorem hullLogVolumeMonotoneObject_image_le_hull :
    (hullLogVolumeMonotoneObject T).logVolume (hullLogVolumeMonotoneObject T).imageSet ≤
      (hullLogVolumeMonotoneObject T).logVolume (hullLogVolumeMonotoneObject T).hull :=
  hullLogVolumeMonotoneObject_logVolume_mono T (s1902ImageSet_subset_hull T)

#check hullLogVolumeMonotoneObject_image_le_hull
#check hullLogVolumeMonotoneObject_logVolume_mono

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeMonotoneObjectActual
end
