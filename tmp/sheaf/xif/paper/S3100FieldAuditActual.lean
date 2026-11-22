import tmp.sheaf.xif.paper.S2725GlobalThetaHullActual
import tmp.sheaf.xif.paper.S2725ThetaImageHullActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.S2725ThetaImageHullActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3100FieldAuditActual

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0,0,0,0,0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The S2725 global hull is actually equal to the image set. -/
theorem S3100_global_hull_eq_image :
    globalThetaHull (C3 := C3) = globalThetaImageSet (C3 := C3) :=
  globalThetaHull_eq_imageSet (C3 := C3)

/-- Image and hull have equal Haar log-volume, not just monotone. -/
theorem S3100_image_logVolume_eq_hull :
    (globalThetaHullInterface (C3 := C3)).logVolume
      (globalThetaHullInterface (C3 := C3)).imageSet =
    (globalThetaHullInterface (C3 := C3)).logVolume
      (globalThetaHullInterface (C3 := C3)).hull := by
  simp only [globalThetaHullInterface]
  rw [globalThetaHull_eq_imageSet]

/-- Hull log-volume is bounded by the unit-region log-volume. -/
theorem S3100_hull_logVolume_le_unit :
    (globalThetaHullInterface (C3 := C3)).logVolume
      (globalThetaHullInterface (C3 := C3)).hull ≤
    (globalThetaHullInterface (C3 := C3)).logVolume
      (globalThetaHullInterface (C3 := C3)).unitRegion := by
  exact le_trans
    ((globalThetaHullInterface (C3 := C3)).logVolume_mono
      (globalThetaHullInterface (C3 := C3)).hull_subset_scaleShift)
    ((globalThetaHullInterface (C3 := C3)).scaleShift_unitRegion_logVolume_le)

/-- Unit-region log-volume is finite. -/
theorem S3100_unit_logVolume_lt_top :
    (globalThetaHullInterface (C3 := C3)).logVolume
      (globalThetaHullInterface (C3 := C3)).unitRegion < ⊤ :=
  (globalThetaHullInterface (C3 := C3)).unitRegion_logVolume_lt_top

/-- Exact first unproved comparison: the global Haar hull log-volume against
the native weighted q-pilot magnitude. -/
def S3100FirstUnprovedInequality
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  ((globalThetaHullInterface (C3 := C3)).logVolume
      (globalThetaHullInterface (C3 := C3)).hull).toReal ≤
    nativeGlobalQPilotNormalizedLogMagnitude (T := T)

#check S3100_global_hull_eq_image
#check S3100_image_logVolume_eq_hull
#check S3100_hull_logVolume_le_unit
#check S3100_unit_logVolume_lt_top
#check S3100FirstUnprovedInequality
#print axioms S3100_image_logVolume_eq_hull
#print axioms S3100_hull_logVolume_le_unit

end LeanFormal.IUT.XiFPaper.S3100FieldAuditActual
end