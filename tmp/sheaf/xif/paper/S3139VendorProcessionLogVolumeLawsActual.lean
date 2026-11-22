import tmp.sheaf.xif.paper.S3139VendorProcessionNormalizedLogVolumeActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: normalized/scaled procession log-volume laws (vendor-adapted, composition)

Vendor-adapted law composition: normalizing then scaling a raw log-volume is the
same as scaling the normalized value; the two adapted structures
(@SourceProcessionNormalizedLogVolume@, @SourceProcessionScaledLogVolume@)
compose consistently.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorProcessionLogVolumeLawsActual

open LeanFormal.IUT.XiFPaper.S3139VendorProcessionNormalizedLogVolumeActual

/-- Normalizing and then scaling composes: the scaled value is the scale times
the normalized raw-minus-offset value. -/
theorem normalizedThenScaled_law (raw normalization scale : ℝ) :
    let V := sourceProcessionNormalizedLogVolumeOf raw normalization
    let S := sourceProcessionScaledLogVolumeOf V.normalizedLogVolume scale
    S.scaledLogVolume = scale * (raw - normalization) := by
  simp [sourceProcessionScaledLogVolumeOf,
    sourceProcessionNormalizedLogVolumeOf]

/-- The normalized value of a raw log-volume equals the raw value minus the
normalization offset (instance law). -/
theorem normalizedLogVolume_eq (raw normalization : ℝ) :
    (sourceProcessionNormalizedLogVolumeOf raw normalization).normalizedLogVolume =
      raw - normalization := rfl

/-- The scaled value of a raw log-volume equals the scale times the raw value
(instance law). -/
theorem scaledLogVolume_eq (raw scale : ℝ) :
    (sourceProcessionScaledLogVolumeOf raw scale).scaledLogVolume =
      scale * raw := rfl

end LeanFormal.IUT.XiFPaper.S3139VendorProcessionLogVolumeLawsActual

end
