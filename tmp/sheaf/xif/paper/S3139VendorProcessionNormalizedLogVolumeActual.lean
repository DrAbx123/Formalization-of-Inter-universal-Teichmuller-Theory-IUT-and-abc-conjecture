import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: procession normalized/scaled log-volume (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/IUTStage1SourceCore.lean:1012
structure IUTStage1ProcessionNormalizedLogVolume: a procession log-volume with
an explicit normalization datum (raw value, normalization, normalized value and
the subtraction law), plus a scaled form with a multiplicative scale.  Both are
constructible for arbitrary real data; they package the normalization step the
paper-route log-volume comparison performs.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorProcessionNormalizedLogVolumeActual

/-- A normalized procession log-volume: raw value, normalization offset, and
the normalized value with the exact subtraction law. -/
structure SourceProcessionNormalizedLogVolume where
  /-- the raw log-volume -/
  rawLogVolume : ℝ
  /-- the normalization offset -/
  normalization : ℝ
  /-- the normalized log-volume -/
  normalizedLogVolume : ℝ
  /-- the normalization law -/
  normalized_law : normalizedLogVolume = rawLogVolume - normalization

/-- Every pair of real data gives a normalized procession log-volume. -/
def sourceProcessionNormalizedLogVolumeOf (raw normalization : ℝ) :
    SourceProcessionNormalizedLogVolume where
  rawLogVolume := raw
  normalization := normalization
  normalizedLogVolume := raw - normalization
  normalized_law := rfl

/-- A scaled procession log-volume: raw value and the scaled value with the
multiplicative scale law. -/
structure SourceProcessionScaledLogVolume where
  /-- the raw log-volume -/
  rawLogVolume : ℝ
  /-- the scale factor -/
  scale : ℝ
  /-- the scaled log-volume -/
  scaledLogVolume : ℝ
  /-- the scaling law -/
  scaled_law : scaledLogVolume = scale * rawLogVolume

/-- Every pair of real data gives a scaled procession log-volume. -/
def sourceProcessionScaledLogVolumeOf (raw scale : ℝ) :
    SourceProcessionScaledLogVolume where
  rawLogVolume := raw
  scale := scale
  scaledLogVolume := scale * raw
  scaled_law := rfl

end LeanFormal.IUT.XiFPaper.S3139VendorProcessionNormalizedLogVolumeActual
