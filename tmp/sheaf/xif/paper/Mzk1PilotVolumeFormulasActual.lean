/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic

/-!
# Mzk1PilotVolumeFormulasActual — exact q-side / Theta-side pilot volume formulas

A520: exact expansions for the faithful Cor 3.12 comparison of
`S3137QThetaPilotLogVolumeReadingsActual`:

* q side: `qPilotLogVolumeReading P = -|log||q||| = log||q||` and
  `exp(reading) = ||q||` (actual completion q of `P.line.C3`);
* Theta side: `thetaPilotHullLogVolume = Haar(log-volume)` of the actual hull,
  `thetaPilotHullLogVolumeReal = log (Haar region).toReal`, finite;
* the named comparison `qThetaPilotLogVolumeComparison` unfolded to
  q-reading <= Theta hull region log-volume;
* the exact p-scaling law of the Theta hull Haar log-volume
  (IUT III Prop. 3.9(i), from `S3137ThetaHullVolumeScalingActual`).

All are true equalities/re-exports of green statements; the comparison itself
remains the named, unproved candidate. No new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PilotVolumeFormulasActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- q side: the actual q-pilot reading is `-|log q|` of the source completion. -/
theorem qPilotLogVolumeReading_eq_neg_abs :
    qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- q side: because the q-candidate is contracting, the reading is the signed
completion log `log||q||`. -/
theorem qPilotLogVolumeReading_eq_log_norm :
    qPilotLogVolumeReading P = Real.log ‖P.line.C3.q.q‖ := by
  have hneg : Real.log ‖P.line.C3.q.q‖ < 0 := by
    have h := localSignedLog_neg P.line.C3.q
    simpa [localSignedLog] using h
  rw [qPilotLogVolumeReading_eq_neg_abs, abs_of_neg hneg, neg_neg]

/-- q side: the reading exponentiates back to the actual completion norm. -/
theorem qPilotLogVolumeReading_exp :
    Real.exp (qPilotLogVolumeReading P) = ‖P.line.C3.q.q‖ := by
  rw [qPilotLogVolumeReading_eq_log_norm, Real.exp_log (qNorm_pos P.line.C3.q)]

/-- q side: the reading is strictly negative. -/
theorem qPilotLogVolumeReading_neg : qPilotLogVolumeReading P < 0 := by
  rw [qPilotLogVolumeReading_eq_log_norm]
  exact localSignedLog_neg P.line.C3.q

/-- Theta side: hull = actual tensor log-shell region. -/
theorem thetaPilotHull_eq_actualRegion :
    thetaPilotHull C3 = actualC3LogShellTensorRegion C3 :=
  thetaPilotHull_eq_region C3

/-- Theta side: the hull Haar log-volume is the region Haar log-volume. -/
theorem thetaPilotHullLogVolume_eq_region :
    thetaPilotHullLogVolume C3 =
      haarLogVolume (actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3) :=
  thetaPilotHullLogVolume_eq_regionLogVolume C3

/-- Theta side: the hull volume is finite. -/
theorem thetaPilotHullLogVolume_ne_top : thetaPilotHullLogVolume C3 ≠ ⊤ :=
  thetaPilotHullLogVolume_ne_top C3

/-- Theta side: the real hull reading is the log of the region Haar measure. -/
theorem thetaPilotHullLogVolumeReal_eq_region :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_regionLogVolume C3

/-- Theta side: exact p-scaling of the hull Haar log-volume
(IUT III Prop. 3.9(i)): multiplying the hull by p shifts the log-volume by
`-dim * log p`. -/
theorem thetaPilotHull_logVolume_p_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real) +
        thetaPilotHullLogVolumeReal C3 :=
  thetaPilotHull_log_measure_prime_smul C3 hpos

/-- The faithful comparison, unfolded to the actual region Haar log-volume. -/
theorem qThetaPilotLogVolumeComparison_iff_actualRegion :
    qThetaPilotLogVolumeComparison C3 P ↔
      qPilotLogVolumeReading P ≤
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal :=
  qThetaPilotLogVolumeComparison_iff_actualRegion C3 P

#check qPilotLogVolumeReading_exp
#check thetaPilotHullLogVolume_eq_region
#check qThetaPilotLogVolumeComparison_iff_actualRegion

end LeanFormal.IUT.XiFPaper.Mzk1PilotVolumeFormulasActual
end
