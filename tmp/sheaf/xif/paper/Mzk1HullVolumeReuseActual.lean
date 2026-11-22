import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.AbsTopIII09ThetaHullScalingActual

/-! Mainline (A511-4): hull-volume readout object REUSING the existing Theta-hull volume
laws instead of reproving them:
* `S3137ThetaHullVolumeScalingActual`: `thetaPilotHull_measure_lt_top`, the p-scaling law
  `thetaPilotHull_log_measure_prime_smul` (IUT III, Prop 3.9 (i)), and
  `thetaPilotHullLogVolumeReal_eq_actualRegion`;
* `AbsTopIII09ThetaHullScalingActual`: re-exports of the same scaling/region identities
  ([AbsTopIII] Prop 5.7 (i)(b), Cor 5.10 (ii)).

The file constructs the hull-volume readout object (theta hull volume + q-pilot volume)
and derives the comparison-candidate equivalence and the p-scaling law from those files
(no re-proof, no shell, no sorry). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullVolumeReuseActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

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
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.AbsTopIII09ThetaHullScalingActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance hullReuseBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance hullReuseBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. The Theta-hull volume reading (reused) -/

/-- The Theta-pilot hull log-volume reading (existing S3137 definition). -/
noncomputable def thetaHullLogVolume : Real :=
  S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHullLogVolumeReal C3

/-- Reused: the hull reading equals the actual C3 tensor region log-volume. -/
theorem thetaHullLogVolume_eq_actualRegion :
    thetaHullLogVolume C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  S3137ThetaHullVolumeScalingActual.thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

/-- Reused: the actual hull container has finite Haar measure. -/
theorem thetaHull_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ :=
  S3137ThetaHullVolumeScalingActual.thetaPilotHull_measure_lt_top (C3 := C3)

/-- Reused p-scaling law (IUT III Prop 3.9 (i)): multiplying the actual hull by `p`
  shifts the Haar log-volume by `-[block : Q_p] * log p`. -/
theorem thetaHull_logVolume_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        thetaHullLogVolume C3 :=
  S3137ThetaHullVolumeScalingActual.thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos

/-! ## 2. The hull-volume readout object -/

/-- The hull-volume readout: the Theta-pilot hull log-volume together with the actual
  q-pilot reading, with their construction equations and the reused finiteness/positivity
  data. -/
structure HullVolumeReadout
    (P : PaperQPilotObjectActual (l := l) (I := I)) where
  /-- The Theta-pilot hull log-volume reading. -/
  thetaHullLogVolume : Real
  thetaHullLogVolume_eq : thetaHullLogVolume =
    S3137QThetaPilotLogVolumeReadingsActual.thetaPilotHullLogVolumeReal C3
  /-- The actual q-pilot log-volume reading `-|log q|`. -/
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = qPilotLogVolumeReading P
  /-- The q reading is nonpositive (actual source completion). -/
  qPilotLogVolume_nonpos : qPilotLogVolume ≤ 0

/-- The hull-volume readout built from the actual data. -/
noncomputable def hullVolumeReadout
    (P : PaperQPilotObjectActual (l := l) (I := I)) : HullVolumeReadout C3 P where
  thetaHullLogVolume := thetaHullLogVolume C3
  thetaHullLogVolume_eq := rfl
  qPilotLogVolume := qPilotLogVolumeReading P
  qPilotLogVolume_eq := rfl
  qPilotLogVolume_nonpos :=
    S3137QThetaPilotLogVolumeReadingsActual.qPilotLogVolumeReading_nonpos P

/-! ## 3. Consumer theorems (comparison candidate + scaling) -/

/-- The comparison candidate of the readout is the existing named candidate
  `qThetaPilotLogVolumeComparison` (S3137), in the readout's own coordinates. -/
theorem hullVolumeReadout_comparison_iff
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    ((hullVolumeReadout C3 P).qPilotLogVolume ≤ (hullVolumeReadout C3 P).thetaHullLogVolume) ↔
      qThetaPilotLogVolumeComparison C3 P :=
  Iff.rfl

/-- The hull readout's p-scaling in its own coordinates (reused theorem restated; the
  Theta-side scaling does not depend on the q-side object). -/
theorem hullVolumeReadout_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        thetaHullLogVolume C3 :=
  thetaHull_logVolume_prime_smul C3 hpos
end

end LeanFormal.IUT.XiFPaper.Mzk1HullVolumeReuseActual