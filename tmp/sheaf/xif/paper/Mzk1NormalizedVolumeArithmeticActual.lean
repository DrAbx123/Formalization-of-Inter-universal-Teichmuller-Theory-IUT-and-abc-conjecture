/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ProcessionNormalizedHullVolumeActual

/-! # A526: arithmetic of the normalized hull volume (p-scaling law) -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The packet-normalized log-volume of the p-scaled region shifts by exactly `-log p`
(the `prime_smul` normalization law of IUT III Prop 3.9, at the actual C3 carrier). -/
theorem packetNormalizedLogVolume_prime_smul
    (S : Set (C3LogShellTensorBlock C3))
    (hpos : 0 < (actualC3LogShellTensorHaar C3) S)
    (hfin : (actualC3LogShellTensorHaar C3) S < ⊤) :
    packetNormalizedLogVolume C3 ((C3.p : ℚ_[C3.p]) • S) =
      -Real.log (C3.p : ℝ) + packetNormalizedLogVolume C3 S := 
  c3PacketNormalizedLogVolume_prime_smul (C3 := C3) (actualC3LogShellTensorHaar C3) hpos hfin

/-- Normalized hull volume of a p-power image: scaling the hull by `p` shifts the
normalized volume by `-log p` (same law, applied to the Theta hull). -/
theorem thetaPilotHullLogVolumeNorm_prime_smul
    (ref : Set (C3LogShellTensorBlock C3))
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3))
    (hfin : (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤) :
    packetNormalizedLogVolume C3 ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3) =
      -Real.log (C3.p : ℝ) + packetNormalizedLogVolume C3 (thetaPilotHull C3) := 
  packetNormalizedLogVolume_prime_smul C3 (thetaPilotHull C3) hpos hfin

/-- **Normalized arithmetic comparison**: if the q-pilot reading is an integral multiple of
`log p` (`qPilotLogVolumeReading P = -k * log p`, i.e. q is the `p^k`-image) and the
normalized hull volume is at most `-k * log p`, then the normalized candidate holds. -/
theorem normCandidate_of_pExponent {P : PaperQPilotObjectActual (l := l) (I := I)}
    (ref : Set (C3LogShellTensorBlock C3)) (k : ℝ)
    (hq : qPilotLogVolumeReading P = -(k * Real.log (C3.p : ℝ)))
    (hbound : -(k * Real.log (C3.p : ℝ)) ≤ thetaPilotHullLogVolumeNorm C3 ref) :
    qThetaPilotLogVolumeComparisonNorm C3 P ref := by
  unfold qThetaPilotLogVolumeComparisonNorm
  rw [hq]
  exact hbound

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual
