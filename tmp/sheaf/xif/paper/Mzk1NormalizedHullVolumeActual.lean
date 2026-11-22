import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

/-! # Normalized hull log-volume object (actual C3 Haar) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1NormalizedHullVolumeActual

open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}

/-- The normalized (procession-normalized) log-volume of the actual Theta-pilot hull. -/
noncomputable def normalizedHullLogVolume
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  thetaPilotHullLogVolumeReal C3

/-- The value is the actual Haar log-volume of the actual C3 tensor region. -/
theorem normalizedHullLogVolume_eq_region
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    normalizedHullLogVolume C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

/-- The hull itself is that region (equality of sets). -/
theorem normalizedHull_eq_region
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    thetaPilotHull C3 = actualC3LogShellTensorRegion C3 :=
  thetaPilotHull_eq_region

/-- Finiteness of the actual hull Haar measure (normalized hull volume is finite). -/
theorem normalizedHull_measure_lt_top
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ := by
  exact thetaPilotHull_measure_lt_top (C3 := C3)

end LeanFormal.IUT.XiFPaper.Mzk1NormalizedHullVolumeActual
