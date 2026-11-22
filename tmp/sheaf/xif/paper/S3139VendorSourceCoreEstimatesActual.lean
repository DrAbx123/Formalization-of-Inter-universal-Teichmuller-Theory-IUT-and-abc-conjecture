import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: local-container log-volume estimates (vendor-adapted)

Adapted from vendor promachina Iut/Stage1/IUTStage1SourceCore.lean:1109
structure IUTStage1LocalContainerLogVolumeEstimate and :1121
IUTStage1LocalObjectContainerLogVolumeEstimate: a local log-volume bounded by a
container log-volume, and the object-vs-container estimate.  Re-proved with our
objects; constructible for arbitrary real data with the required inequality.

**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139VendorSourceCoreEstimatesActual

/-- A local-container log-volume estimate: the local value is bounded by the
container value (vendor IUTStage1LocalContainerLogVolumeEstimate). -/
structure SourceLocalContainerLogVolumeEstimate where
  /-- the local log-volume -/
  localValue : ℝ
  /-- the container log-volume -/
  containerValue : ℝ
  /-- the estimate -/
  local_le_container : localValue ≤ containerValue

/-- Every pair of real data with the required inequality gives a local-container
log-volume estimate. -/
def sourceLocalContainerLogVolumeEstimateOf (localValue containerValue : ℝ)
    (h : localValue ≤ containerValue) : SourceLocalContainerLogVolumeEstimate where
  localValue := localValue
  containerValue := containerValue
  local_le_container := h

/-- An object-container log-volume estimate: the local object value is bounded by
the container value times the object count bound (vendor
IUTStage1LocalObjectContainerLogVolumeEstimate). -/
structure SourceLocalObjectContainerLogVolumeEstimate where
  /-- the local object log-volume -/
  objectValue : ℝ
  /-- the container log-volume -/
  containerValue : ℝ
  /-- the object count bound -/
  objectCount : ℕ
  /-- the count times local bound is at most the container value -/
  object_le_container : (objectCount : ℝ) * objectValue ≤ containerValue

/-- Every triple of real data with the required inequality gives an
object-container log-volume estimate. -/
def sourceLocalObjectContainerLogVolumeEstimateOf (objectValue containerValue : ℝ)
    (objectCount : ℕ)
    (h : (objectCount : ℝ) * objectValue ≤ containerValue) :
    SourceLocalObjectContainerLogVolumeEstimate where
  objectValue := objectValue
  containerValue := containerValue
  objectCount := objectCount
  object_le_container := h

end LeanFormal.IUT.XiFPaper.S3139VendorSourceCoreEstimatesActual
