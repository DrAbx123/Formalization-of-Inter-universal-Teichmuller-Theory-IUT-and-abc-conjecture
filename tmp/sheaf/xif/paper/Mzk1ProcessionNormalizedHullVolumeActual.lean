/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-!
# A526 procession-normalized Theta-pilot hull log-volume

The S3137 reading `thetaPilotHullLogVolumeReal = log Haar(thetaPilotHull)` uses an
UNNORMALIZED addHaar measure (determined only up to an additive constant), so
`Q_C <= H_C` depends on the normalization choice.  Paper uses the procession-normalized
mono-analytic log-volume (IUT III Proposition 3.9), where a reference region has
log-volume 0.

Construction:
* `c3PacketNormalizedLogVolume mu S = log (mu S).toReal / [block : Q_p]`
  (S3137 packet normalization; the p-scaling law is proved there);
* `normalizedLogVolume mu ref S := c3PacketNormalizedLogVolume mu S -
  c3PacketNormalizedLogVolume mu ref` (reference `ref` has normalized value 0);
* `thetaPilotHullLogVolumeNorm := normalizedLogVolume mu (actualUnitRegion C3) thetaPilotHull`.

Proved here:
* the ratio form `thetaNorm = Real.log ((mu hull).toReal / (mu unit).toReal) / dim`
  (`Real.log_div`), i.e. the normalized reading;
* `thetaNorm * dim = log(mu hull) - log(mu unit)`: comparison with the unnormalized Haar
  reading differs by the fixed reference constant;
* the normalized reading is INVARIANT under `p`-scaling of both regions (the p-shift
  cancels), the hallmark of the procession normalization;
* the S3137 named comparison is restated in normalized form; the q side stays
  `qPilotLogVolumeReading P = -|log q|`.  The truth of the normalized comparison is the
  named candidate; no same-region identity is used (the reference is the unit region).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual

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
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance normBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance normBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-! ## 1. The reference region and the normalized log-volume -/

/-- The reference region for the normalization: the actual unit region of the C3
  log-shell tensor packet (its normalized log-volume is set to 0). -/
def normalizationReference : Set (C3LogShellTensorBlock C3) :=
  actualUnitRegion C3

/-- The normalized log-volume relative to a reference region: the difference of the
  packet-normalized (dimension-divided) log-volumes; the reference has value 0. -/
noncomputable def normalizedLogVolume
    (μ : Measure (C3LogShellTensorBlock C3))
    (ref S : Set (C3LogShellTensorBlock C3)) : ℝ :=
  c3PacketNormalizedLogVolume C3 μ S - c3PacketNormalizedLogVolume C3 μ ref

/-- The reference region has normalized log-volume 0. -/
@[simp] theorem normalizedLogVolume_self
    (μ : Measure (C3LogShellTensorBlock C3))
    (ref : Set (C3LogShellTensorBlock C3)) :
    normalizedLogVolume C3 μ ref ref = 0 :=
  sub_self _

/-- The packet-normalized log-volume in terms of the Haar measure and the block
  dimension. -/
theorem packetNormalizedLogVolume_eq_log_div_dim
    (μ : Measure (C3LogShellTensorBlock C3))
    (S : Set (C3LogShellTensorBlock C3)) :
    c3PacketNormalizedLogVolume C3 μ S =
      Real.log (μ S).toReal / (c3TensorBlockDimension C3 : ℝ) :=
  rfl

/-! ## 2. The normalized Theta-pilot hull log-volume -/

/-- **The procession-normalized Theta-pilot hull log-volume**: the packet-normalized
  hull volume relative to the unit region (reference value 0). -/
noncomputable def thetaPilotHullLogVolumeNorm : ℝ :=
  normalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
    (normalizationReference C3) (thetaPilotHull C3)

/-- The normalized hull volume is the reference-relative packet-normalized volume. -/
theorem thetaPilotHullLogVolumeNorm_eq :
    thetaPilotHullLogVolumeNorm C3 =
      c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) -
        c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
          (normalizationReference C3) :=
  rfl

/-- **Ratio form** of the normalized reading (`Real.log_div`): the difference of the
  dimension-divided Haar log-volumes is the log of the Haar-measure ratio divided by the
  block dimension. -/
theorem thetaPilotHullLogVolumeNorm_eq_log_div
    (hH : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3))
    (hR : 0 < (actualC3LogShellTensorHaar C3) (normalizationReference C3)) :
    thetaPilotHullLogVolumeNorm C3 =
      Real.log (((actualC3LogShellTensorHaar C3) (thetaPilotHull C3)).toReal /
        ((actualC3LogShellTensorHaar C3) (normalizationReference C3)).toReal) /
        (c3TensorBlockDimension C3 : ℝ) := by
  unfold thetaPilotHullLogVolumeNorm normalizedLogVolume c3PacketNormalizedLogVolume
  rw [← sub_div, ← Real.log_div (ne_of_gt hH) (ne_of_gt hR)]

/-- **Comparison with the unnormalized Haar reading**: multiplying the normalized
  reading by the block dimension differs from the unnormalized hull log-volume by the
  fixed reference constant `log (haar unit)`. -/
theorem thetaPilotHullLogVolumeNorm_mul_dim :
    thetaPilotHullLogVolumeNorm C3 * (c3TensorBlockDimension C3 : ℝ) =
      thetaPilotHullLogVolumeReal C3 -
        Real.log ((actualC3LogShellTensorHaar C3)
          (normalizationReference C3)).toReal := by
  have hdim : (c3TensorBlockDimension C3 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  unfold thetaPilotHullLogVolumeNorm normalizedLogVolume c3PacketNormalizedLogVolume
    thetaPilotHullLogVolumeReal
  field_simp
  ring

/-! ## 3. Invariance of the normalized reading under p-scaling -/

/-- **Normalization invariance**: scaling both the region and the reference by `p`
  leaves the normalized log-volume unchanged (the `-log p` packet shift cancels). -/
theorem normalizedLogVolume_prime_smul
    (μ : Measure (C3LogShellTensorBlock C3)) [Measure.IsAddHaarMeasure μ]
    {ref S : Set (C3LogShellTensorBlock C3)}
    (href_pos : 0 < μ ref) (href_fin : μ ref < ⊤)
    (hS_pos : 0 < μ S) (hS_fin : μ S < ⊤) :
    normalizedLogVolume C3 μ ((C3.p : ℚ_[C3.p]) • ref) ((C3.p : ℚ_[C3.p]) • S) =
      normalizedLogVolume C3 μ ref S := by
  unfold normalizedLogVolume
  rw [c3PacketNormalizedLogVolume_prime_smul C3 μ href_pos href_fin,
    c3PacketNormalizedLogVolume_prime_smul C3 μ hS_pos hS_fin]
  ring

/-! ## 4. The normalized S3137 comparison (q side stays the paper reading) -/

variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- The paper q-pilot reading `-|log q|` (S3137; NOT a region log-volume). -/
def qPilotLogVolume : ℝ :=
  qPilotLogVolumeReading P

/-- The q reading is `-|log q|`. -/
theorem qPilotLogVolume_eq_neg_abs :
    qPilotLogVolume C3 P = -|Real.log (‖P.line.C3.q.q‖)| :=
  qPilotLogVolumeReading_eq_neg_abs_qParameter P

/-- The q reading is nonpositive. -/
theorem qPilotLogVolume_nonpos : qPilotLogVolume C3 P ≤ 0 :=
  qPilotLogVolumeReading_nonpos P

/-- **The normalized S3137 comparison candidate**: the q-pilot reading is at most the
  procession-normalized hull volume.  This is the paper-shaped comparison under the
  normalization; its truth is the named candidate (no same-region identity is used: the
  hull is compared with the UNIT region reference, not with itself). -/
def qThetaComparisonNorm : Prop :=
  qPilotLogVolume C3 P ≤ thetaPilotHullLogVolumeNorm C3

/-- The normalized comparison is the named S3137 candidate restated. -/
theorem qThetaComparisonNorm_iff :
    qThetaComparisonNorm C3 P ↔ qPilotLogVolume C3 P ≤ thetaPilotHullLogVolumeNorm C3 :=
  Iff.rfl

/-- The signed normalized comparison data and its StepXI contract. -/
structure NormalizedComparison where
  /-- The q-pilot reading `-|log q|`. -/
  qSigned : ℝ
  /-- The normalized Theta-pilot hull volume `-|log(Theta)|` (procession normalization). -/
  thetaSigned : ℝ
  qSigned_eq : qSigned = qPilotLogVolume C3 P
  thetaSigned_eq : thetaSigned = thetaPilotHullLogVolumeNorm C3
  qSigned_neg : qSigned < 0
  /-- The normalized comparison (named candidate). -/
  comparison : qSigned ≤ thetaSigned

/-- Cor 3.12 ordered conclusion from the normalized comparison data. -/
def normalizedContract (D : NormalizedComparison C3 P) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) : StepXIContract where
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
  target_le_theta := D.comparison

theorem cor312Conclusion_of_normalized (D : NormalizedComparison C3 P)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion (normalizedContract C3 P D ipl she apt hipl hshe hapt) :=
  cor312_of_constructed_stepXI _

end

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionNormalizedHullVolumeActual