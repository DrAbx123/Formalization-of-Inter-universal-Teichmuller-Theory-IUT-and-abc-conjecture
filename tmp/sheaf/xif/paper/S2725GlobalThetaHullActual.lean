import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance s2725MeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance s2725BorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual carrier: the C3 log-shell tensor block, definitionally the
arithmetic tuple block of the C3 tensor places and tuple. -/
abbrev GlobalThetaCarrier : Type := C3LogShellTensorBlock C3

/-- The actual theta-pilot image set: the C3 tensor log-shell integral region. -/
def globalThetaImageSet : Set (GlobalThetaCarrier (C3 := C3)) :=
  actualC3LogShellTensorRegion C3

/-- The actual holomorphic hull: the literal least lambda-O hull of the image
set inside the C3 tensor block. -/
def globalThetaHull : Set (GlobalThetaCarrier (C3 := C3)) :=
  actualHolomorphicHull C3 (globalThetaImageSet (C3 := C3))

theorem globalThetaHull_eq_imageSet :
    globalThetaHull (C3 := C3) = globalThetaImageSet (C3 := C3) := by
  simpa [globalThetaHull, globalThetaImageSet, actualUnitRegion]
    using actualHolomorphicHull_unitRegion_eq (C3 := C3)

theorem globalThetaImageSet_subset_hull :
    globalThetaImageSet (C3 := C3) ⊆ globalThetaHull (C3 := C3) := by
  rw [globalThetaHull_eq_imageSet]

theorem globalThetaImageSet_compact :
    IsCompact (globalThetaImageSet (C3 := C3)) :=
  actualC3LogShellTensorRegion_compact C3

theorem globalThetaHull_compact :
    IsCompact (globalThetaHull (C3 := C3)) := by
  rw [globalThetaHull_eq_imageSet]
  exact globalThetaImageSet_compact (C3 := C3)

/-- The actual global unit region on the C3 tensor block. -/
def globalThetaUnitRegion : Set (GlobalThetaCarrier (C3 := C3)) :=
  actualUnitRegion C3

theorem globalThetaUnitRegion_eq_imageSet :
    globalThetaUnitRegion (C3 := C3) = globalThetaImageSet (C3 := C3) := rfl

/-- The actual nonzero scaling used by the lambda-O hull: scaling by 1. -/
def globalThetaScaleShift (x : GlobalThetaCarrier (C3 := C3)) :
    GlobalThetaCarrier (C3 := C3) := (1 : GlobalThetaCarrier (C3 := C3)) * x

theorem globalThetaScaleShift_eq_id (x : GlobalThetaCarrier (C3 := C3)) :
    globalThetaScaleShift (C3 := C3) x = x := by
  unfold globalThetaScaleShift
  rw [one_mul]

theorem globalThetaScaleShift_unitRegion_eq :
    globalThetaScaleShift (C3 := C3) '' globalThetaUnitRegion (C3 := C3) =
      actualScaledRegion C3 (1 : GlobalThetaCarrier (C3 := C3)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

/-- The actual Haar log-volume on the C3 tensor block. -/
noncomputable def globalThetaLogVolume :
    Set (GlobalThetaCarrier (C3 := C3)) → ENNReal :=
  fun S => haarLogVolume (actualC3LogShellTensorHaar C3) S

theorem globalThetaLogVolume_mono {S T : Set (GlobalThetaCarrier (C3 := C3))}
    (hST : S ⊆ T) :
    globalThetaLogVolume (C3 := C3) S ≤ globalThetaLogVolume (C3 := C3) T :=
  haarLogVolume_mono (μ := actualC3LogShellTensorHaar C3) hST

theorem globalThetaUnitRegion_logVolume_lt_top :
    globalThetaLogVolume (C3 := C3) (globalThetaUnitRegion (C3 := C3)) < ⊤ := by
  have hfin : actualC3LogShellTensorHaar C3
      (actualUnitRegion C3) < ⊤ :=
    IsCompact.measure_lt_top (actualC3LogShellTensorRegion_compact C3)
  unfold globalThetaLogVolume globalThetaUnitRegion
  rw [haarLogVolume_of_lt_top hfin]
  exact ENNReal.ofReal_lt_top

/-- The actual global Theta-pilot IQ hull log-volume interface on the C3 tensor
block, using the actual image set, actual least lambda-O hull, actual Haar
measure and the actual unit region. -/
noncomputable def globalThetaHullInterface :
    IQHullLogVolumeInterface (GlobalThetaCarrier (C3 := C3)) where
  imageSet := globalThetaImageSet (C3 := C3)
  hull := globalThetaHull (C3 := C3)
  imageSet_subset_hull := globalThetaImageSet_subset_hull (C3 := C3)
  logVolume := globalThetaLogVolume (C3 := C3)
  logVolume_mono := globalThetaLogVolume_mono (C3 := C3)
  unitRegion := globalThetaUnitRegion (C3 := C3)
  scaleShift := globalThetaScaleShift (C3 := C3)
  hull_subset_scaleShift := by
    intro x hx
    rw [globalThetaHull_eq_imageSet] at hx
    rw [globalThetaUnitRegion_eq_imageSet]
    exact ⟨x, hx, by rw [globalThetaScaleShift_eq_id]⟩
  unitRegion_logVolume_lt_top := globalThetaUnitRegion_logVolume_lt_top (C3 := C3)
  scaleShift_unitRegion_logVolume_le := by
    rw [globalThetaScaleShift_unitRegion_eq]
    have hunit : actualScaledRegion C3 (1 : GlobalThetaCarrier (C3 := C3)) =
        globalThetaUnitRegion (C3 := C3) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [globalThetaUnitRegion] using hy
      · intro hx
        exact ⟨x, hx, by rw [one_mul]⟩
    rw [hunit]

#check GlobalThetaCarrier
#check globalThetaImageSet
#check globalThetaHull
#check globalThetaHull_eq_imageSet
#check globalThetaImageSet_compact
#check globalThetaHullInterface
#print axioms globalThetaHullInterface

end LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
end
