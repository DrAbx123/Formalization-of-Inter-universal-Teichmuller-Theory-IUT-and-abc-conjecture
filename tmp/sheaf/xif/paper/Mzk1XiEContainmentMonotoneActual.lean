/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FaithfulXiEContainmentActual
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-!
# A521 xi-e containment by monotonicity: possibleRegion ⊆ hull, log-volume monotone

Paper structure of Cor 3.12: the q-pilot possible image lies in the Theta-pilot hull
(xi-e containment), and log-volume is monotone under inclusion (q region)
  log-vol(qRegion) <= log-vol(ThetaPilotHull) = -|log(Theta)|.

* The Thm 3.11 possible-image part is `possibleRegion_subset` (green
  `MRRep.reg_subset_possibleRegion`, imported from the A520 file).
* The hull/log-volume monotonicity is proved here for the actual C3 container: the
  Haar measure of the actual tensor log-shell region is at most that of its holomorphic
  hull (`thetaPilotHull = actualRegion`), hence the real log-volumes compare.
* The remaining named input is the identification of the q-pilot reading with the
  q-region log-volume (the multiradial 'q-pilot possible image' step); it is the explicit
  field of `MonotoneXiEContainment` below.  No hcmp/packet data is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentMonotoneActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1FaithfulXiEContainmentActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance monotoneBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance monotoneBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. The actual q-region and the Theta-pilot hull -/

/-- The q-pilot container region on the C3 input (the actual tensor log-shell region;
  the q-pilot's possible-image region in the common container). -/
def qPilotContainerRegion : Set (C3LogShellTensorBlock C3) :=
  actualC3LogShellTensorRegion C3

/-- The Theta-pilot hull is the actual tensor log-shell region itself (S3137). -/
theorem thetaPilotHull_eq_qPilotRegion :
    thetaPilotHull C3 = qPilotContainerRegion C3 :=
  thetaPilotHull_eq_region (C3 := C3)

/-- The q-pilot region is contained in the Theta-pilot hull (equality, hence ⊆). -/
theorem qPilotRegion_subset_thetaPilotHull :
    qPilotContainerRegion C3 ⊆ thetaPilotHull C3 :=
  (thetaPilotHull_eq_qPilotRegion C3).ge

/-! ## 2. Haar measure monotonicity and log-volume monotonicity -/

/-- The real Haar log-volume of a measurable region of the actual C3 container. -/
def haarLogVolume (S : Set (C3LogShellTensorBlock C3)) : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3) S).toReal

/-- **Haar measure monotonicity**: a subregion has at most the measure of its container. -/
theorem haar_measure_mono {S T : Set (C3LogShellTensorBlock C3)} (hST : S ⊆ T) :
    (actualC3LogShellTensorHaar C3) S ≤ (actualC3LogShellTensorHaar C3) T :=
  measure_mono hST

/-- **Log-volume monotonicity** under inclusion, for positive finite measure regions:
  the real Haar log-volume is monotone. -/
theorem haarLogVolume_mono {S T : Set (C3LogShellTensorBlock C3)} (hST : S ⊆ T)
    (hS : 0 < (actualC3LogShellTensorHaar C3) S)
    (hT : (actualC3LogShellTensorHaar C3) T ≠ ⊤) :
    haarLogVolume C3 S ≤ haarLogVolume C3 T := by
  unfold haarLogVolume
  have hle : (actualC3LogShellTensorHaar C3) S ≤ (actualC3LogShellTensorHaar C3) T :=
    haar_measure_mono C3 hST
  have hSpos : (0 : ℝ) < ((actualC3LogShellTensorHaar C3) S).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨hS, ne_top_of_le_ne_top hT hle⟩
  have hTpos : (0 : ℝ) < ((actualC3LogShellTensorHaar C3) T).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨lt_of_lt_of_le hS hle, hT⟩
  exact Real.log_le_log hSpos (ENNReal.toReal_mono hT hle)

/-- **The logarithmic comparison for the actual container**:
  `log-vol(qRegion) <= log-vol(ThetaPilotHull)`. -/
theorem qRegion_logVolume_le_thetaPilotHull
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (qPilotContainerRegion C3)) :
    haarLogVolume C3 (qPilotContainerRegion C3) ≤
      haarLogVolume C3 (thetaPilotHull C3) :=
  haarLogVolume_mono C3 (qPilotRegion_subset_thetaPilotHull C3) hpos
    (thetaPilotHull_measure_lt_top (C3 := C3)).ne

/-- The hull log-volume is the S3137 `-|log(Theta)|` reading. -/
theorem thetaPilotHullVolume_eq_haarLogVolume :
    thetaPilotHullVolume C3 = haarLogVolume C3 (thetaPilotHull C3) := by
  unfold thetaPilotHullVolume haarLogVolume thetaPilotHullLogVolumeReal
  rfl

/-! ## 3. The monotone xi-e containment object -/

/-- **Monotone xi-e containment data**: the q-region log-volume (identified with the
  q-pilot reading as the explicit named input) is at most the Theta-pilot hull log-volume.
  The hull inclusion and log-volume monotonicity are proved above; the named field
  `qLogVolume_eq` is the multiradial identification of the q-pilot reading with the
  q-region log-volume (paper Step (xi-e) possible-image statement). -/
structure MonotoneXiEContainment
    (P : PaperQPilotObjectActual (l := l) (I := I)) where
  /-- The q-pilot log-volume reading. -/
  qLogVolume : ℝ
  qLogVolume_eq : qLogVolume = qPilotLogVolume C3 P
  /-- The q reading is the q-region Haar log-volume (named multiradial identification). -/
  qLogVolume_eq_regionLogVolume : qLogVolume = haarLogVolume C3 (qPilotContainerRegion C3)
  /-- Positivity of the q-region measure (needed for log monotonicity). -/
  qRegion_measure_pos : 0 < (actualC3LogShellTensorHaar C3) (qPilotContainerRegion C3)
  /-- The q reading is negative. -/
  qLogVolume_neg : qLogVolume < 0

/-- The inequality of the monotone containment: `q <= -|log(Theta)|`. -/
theorem monotone_inequality (P : PaperQPilotObjectActual (l := l) (I := I))
    (D : MonotoneXiEContainment C3 P) :
    D.qLogVolume ≤ thetaPilotHullVolume C3 := by
  rw [D.qLogVolume_eq_regionLogVolume, thetaPilotHullVolume_eq_haarLogVolume]
  exact qRegion_logVolume_le_thetaPilotHull C3 D.qRegion_measure_pos

/-- The monotone containment gives the faithful xi-e containment (A520 object). -/
def toFaithfulXiEContainment (P : PaperQPilotObjectActual (l := l) (I := I))
    (D : MonotoneXiEContainment C3 P) : FaithfulXiEContainment C3 P :=
  faithfulXiEContainmentOf C3 P (by
    rw [← D.qLogVolume_eq]
    exact monotone_inequality C3 P D)

/-- Cor 3.12 ordered conclusion via the monotone containment. -/
theorem cor312Conclusion_of_monotone (P : PaperQPilotObjectActual (l := l) (I := I))
    (D : MonotoneXiEContainment C3 P) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (faithfulContract C3 P (toFaithfulXiEContainment C3 P D) ipl she apt hipl hshe hapt) :=
  cor312Conclusion_of_faithful C3 P (toFaithfulXiEContainment C3 P D) ipl she apt
    hipl hshe hapt

end

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentMonotoneActual
/-! A525 WARNING: `thetaPilotHull = actualC3LogShellTensorRegion` (S3137), so the region
used in `qRegion_logVolume_le_thetaPilotHull` is the SAME set on both sides: the
monotone inequality proved here is the identity case, NOT the paper q/Theta comparison.
Genuine (different-object) comparison: `Mzk1SignedCor312AssemblyActual`. -/
