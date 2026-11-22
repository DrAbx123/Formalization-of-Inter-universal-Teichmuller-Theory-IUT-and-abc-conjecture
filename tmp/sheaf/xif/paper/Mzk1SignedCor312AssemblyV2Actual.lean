/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# A525 signed 3.12 assembly, rename-free (v2; original file being concurrently edited)

Readings are the two distinct S3137 paper objects:
* q side: `qPilotLogVolumeReading P = -|log q|`;
* Theta side: `thetaPilotHullLogVolumeReal C3` (Haar log-volume of the Theta hull).
S3137 proves `thetaPilotHull = actualC3LogShellTensorRegion`, so any region-based readings
of the two are literally equal — a rename, not the paper comparison (documented by
`signedLogVolume_region_rename_obstruction`).  The comparison itself stays the named
candidate `qThetaPilotLogVolumeComparison`; the reduction to `StepXIContract` /
`Cor312Conclusion` is proved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1SignedCor312AssemblyV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The signed log-volume of a region of the actual C3 container. -/
def signedLogVolume (S : Set (C3LogShellTensorBlock C3)) : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3) S).toReal

/-- The actual tensor log-shell region (the q-side region of S3137). -/
def qRegion : Set (C3LogShellTensorBlock C3) := 
  actualC3LogShellTensorRegion C3

/-- The actual Theta-pilot hull (proved equal to the tensor region by S3137). -/
def thetaHull : Set (C3LogShellTensorBlock C3) := 
  thetaPilotHull C3

/-- S3137: the Theta hull is literally the tensor region. -/
theorem thetaHull_eq_qRegion : thetaHull C3 = qRegion C3 :=
  thetaPilotHull_eq_region (C3 := C3)

/-- **Rename obstruction (A525)**: the region-based readings coincide trivially. -/
theorem signedLogVolume_region_rename_obstruction :
    signedLogVolume C3 (qRegion C3) = signedLogVolume C3 (thetaHull C3) := by
  rw [thetaHull_eq_qRegion (C3 := C3)]

/-- The signed readings using only the two distinct S3137 paper objects. -/
structure SignedReadings (P : PaperQPilotObjectActual (l := l) (I := I)) where
  /-- `-|log q|`. -/
  qSigned : ℝ
  /-- `Real.log (haar (thetaPilotHull)).toReal`. -/
  thetaSigned : ℝ
  qSigned_eq_paper : qSigned = qPilotLogVolumeReading P
  thetaSigned_eq_paper : thetaSigned = thetaPilotHullLogVolumeReal C3
  qSigned_neg : qSigned < 0

/-- Canonical readings from S3137 objects. -/
def SignedReadings.paper {P : PaperQPilotObjectActual (l := l) (I := I)}
    (hqneg : qPilotLogVolumeReading P < 0) : SignedReadings C3 P where
  qSigned := qPilotLogVolumeReading P
  thetaSigned := thetaPilotHullLogVolumeReal C3
  qSigned_eq_paper := rfl
  thetaSigned_eq_paper := rfl
  qSigned_neg := hqneg

/-- Candidate ⇒ signed inequality (the candidate is exactly this inequality). -/
theorem signedReadings_inequality_of_candidate {P : PaperQPilotObjectActual (l := l) (I := I)}
    (D : SignedReadings C3 P) (hcmp : qThetaPilotLogVolumeComparison C3 P) :
    D.qSigned ≤ D.thetaSigned := by
  rw [D.qSigned_eq_paper, D.thetaSigned_eq_paper]
  exact hcmp

/-- StepXI contract from the signed readings (ordering by the named candidate). -/
def signedContract {P : PaperQPilotObjectActual (l := l) (I := I)}
    (D : SignedReadings C3 P) (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
  qSigned := D.qSigned
  thetaSigned := D.thetaSigned
  targetSigned := D.qSigned
  q_negative := D.qSigned_neg
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := le_rfl
  target_le_theta := signedReadings_inequality_of_candidate C3 D hcmp

/-- Cor 3.12 ordered conclusion (under the named candidate). -/
theorem cor312Conclusion_of_signedReadings {P : PaperQPilotObjectActual (l := l) (I := I)}
    (D : SignedReadings C3 P) (hcmp : qThetaPilotLogVolumeComparison C3 P)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion := 
  cor312_of_constructed_stepXI _

end LeanFormal.IUT.XiFPaper.Mzk1SignedCor312AssemblyV2Actual
