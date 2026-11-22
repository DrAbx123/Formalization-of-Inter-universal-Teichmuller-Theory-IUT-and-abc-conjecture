/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312PaperReadoutConsumerActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetBridgeActual
import tmp.sheaf.xif.paper.Mzk1P0QVFamNormBridgeDonorActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.PaperBadPlaceTensorGeometryActual
import Mathlib.Tactic

/-! # Actual reading target: same-source one-way transport (R: Q_src ≤ Q_norm ≤ H_root ≤ H_target)

This file replaces the (too strong, and wrong-direction) G2/G3 EQUALITY bridge by the
one-way transport from `coord/P7-READING-FIRST-ATTACK-20261114.md` §2:

* `Q_src`  = `qPilotLogVolumeReading P` (raw source q reading, negative log);
* `Q_norm` = `actualQPilotSignedLogClassical T` (normalized signed q scalar);
* `H_root` = `actualThetaHullLogRoot T` (actual normalized root-hull log);
* `H_tgt`  = `thetaPilotHullLogVolumeReal C3` (raw target Haar log reading).

The MIDDLE arrow `Q_norm ≤ H_root` is GREEN: it is exactly
`PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget` (actual root-hull containment
`qPilotNormRegion ⊆ rootThetaHull`, per-b monotone normalized log; no S45, no ratio=1,
no default-norm model, no sorry/axiom; probe: three axioms).

The two REMAINING arrows are recorded as explicit one-way conditions (NOT equalities,
NOT new assumptions of the final theorem, and NOT faked):
* (R1) `Q_src ≤ Q_norm`: same-q-witness identification + `log n_def ≤ log n_norm`
  (from the donor power bridge `n_norm = n_def^(1/d)` with `0<n_def<1`, `d≥1`, i.e.
  `qVFamNormRatio ≥ 1`), plus the same-weight/index correspondence;
* (R3) `H_root ≤ H_tgt`: the actual root-hull region (its `oneLabel` branch and the
  integer lattice it generates) enters the frozen target hull `thetaPilotHull C3`, and
  the two Haar log readings are calibrated (normalized-log vs raw-log: reference mass
  and tensor degree — `raw = d·normalized + log μ(R)`).

No G2/G3 equality is asserted; `normRatio = 1` is NOT used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetBridgeActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual
open LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperReadoutConsumerActual
open MeasureTheory

universe u v

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable {V : Type} (I : OriginalInput l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- (R1) Same-q-witness, one-way: the raw source q reading is at most the normalized
signed q scalar.  Uses `log n_def ≤ log n_norm` (donor power bridge with ratio ≥ 1)
and the same-weight/index correspondence. -/
def QSourceLeQNorm : Prop :=
  qPilotLogVolumeReading P ≤ actualQPilotSignedLogClassical (l := l) T

/-- (R3) Root-hull into target hull, one-way, with measure calibration: the actual
normalized root-hull log is at most the raw target Haar log reading.  Uses the
`oneLabel` branch and its integer lattice entering `thetaPilotHull C3`, plus the
normalized-vs-raw calibration `raw = d·normalized + log μ(R)`. -/
def HRootLeHTarget : Prop :=
  actualThetaHullLogRoot (l := l) T ≤ thetaPilotHullLogVolumeReal C3

/-- Per-b comparison: **IF** the qVFam default norm is the norm of the SAME base q
(the missing family/place identification), then `c_norm * log p ≤ baseQLogMagnitude`
(normalized log is at most the base log, donor ratio ≥ 1 direction). -/
theorem qVFamCoefficient_mul_log_le_baseQLogMagnitude
    (b : Bad (nativePlaceSelection T))
    (hq : qVFamDefaultNorm T b = ‖(baseQ T b).q‖) :
    QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b *
      Real.log (qVFamTensorP T b : Real) ≤ baseQLogMagnitude T b := by
  have hdefpos : 0 < qVFamDefaultNorm T b :=
    Mzk1P0QVFamNormBridgeDonorActual.qVFamDefaultNorm_pos T b
  have hle : qVFamDefaultNorm T b ≤ qVFamNormalizedNorm T b := by
    have hratio : 1 ≤ qVFamNormRatio T b :=
      Mzk1P0QVFamNormBridgeDonorActual.qVFamNormRatio_ge_one T b
    unfold qVFamNormRatio at hratio
    exact (one_le_div hdefpos).mp hratio
  rw [QVFamNormalizedCoefficientBridgeActual.qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm]
  have hbase : baseQLogMagnitude T b = -Real.log (qVFamDefaultNorm T b) := by
    unfold BaseQLogVolumeActual.baseQLogMagnitude localLogMagnitude localSignedLog
    rw [hq]
  rw [hbase]
  have hlog := Real.log_le_log hdefpos hle
  linarith

/-- Sum form: **IF** qVFam default norms agree with the base q norms at every bad place,
then the qVFam normalized magnitude is at most the native global base magnitude
(correct direction; equality would be S45-like and false for d>1). -/
theorem actualQPilotMagnitudeClassical_le_nativeGlobal_of_same_q
    (h : ∀ b : Bad (nativePlaceSelection T), qVFamDefaultNorm T b = ‖(baseQ T b).q‖) :
    actualQPilotMagnitudeClassical (l := l) T ≤
      nativeGlobalQPilotNormalizedLogMagnitude T := by
  rw [NativeGlobalQPilotNormalizedLogVolumeActual.nativeGlobalQPilotNormalizedLogMagnitude_eq]
  unfold actualQPilotMagnitudeClassical
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (qVFamCoefficient_mul_log_le_baseQLogMagnitude T b (h b))
    (PaperBadPlaceTensorGeometryActual.badPlaceNativeBadLocalWeight_nonneg T b)

/-- **R1 numeric core (GREEN)**: at each bad place the DEFAULT canonical norm is at
most the NORMALIZED norm (`qVFamNormRatio ≥ 1` and default norm positive), hence its
log is at most the normalized log.  This is the favorable-direction inequality that
replaces `normRatio = 1`. -/
theorem qVFamDefaultNorm_le_qVFamNormalizedNorm (b : Bad (nativePlaceSelection T)) :
    qVFamDefaultNorm T b ≤ qVFamNormalizedNorm T b := by
  have hpos : 0 < qVFamDefaultNorm T b := Mzk1P0QVFamNormBridgeDonorActual.qVFamDefaultNorm_pos T b
  have hratio : 1 ≤ qVFamNormRatio T b := Mzk1P0QVFamNormBridgeDonorActual.qVFamNormRatio_ge_one T b
  unfold qVFamNormRatio at hratio
  exact (one_le_div hpos).mp hratio

theorem log_qVFamDefaultNorm_le_log_normalized (b : Bad (nativePlaceSelection T)) :
    Real.log (qVFamDefaultNorm T b) ≤ Real.log (qVFamNormalizedNorm T b) :=
  Real.log_le_log (Mzk1P0QVFamNormBridgeDonorActual.qVFamDefaultNorm_pos T b)
    (qVFamDefaultNorm_le_qVFamNormalizedNorm T b)

/-- **Middle arrow is GREEN**: actual hull containment gives
`Q_norm ≤ H_root` (no S45, no ratio=1). -/
theorem qNorm_le_hRoot :
    actualQPilotSignedLogClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T :=
  actualPaperXiFTarget (l := l) T

/-- **Original reading line from the one-way transport**:
`Q_src ≤ Q_norm ≤ H_root ≤ H_tgt`.  The middle arrow is proved; the two outer
arrows are the explicit remaining conditions (same q witness/ratio and root-hull
into-target with measure calibration). -/
theorem qPilotLogVolumeReading_le_thetaPilotHullLogVolumeReal_of_transport
    (hQ : QSourceLeQNorm (T := T) (I := I) (P := P))
    (hH : HRootLeHTarget (T := T) (I := I) (C3 := C3)) :
    qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 := by
  have hmid := qNorm_le_hRoot (T := T)
  unfold QSourceLeQNorm at hQ
  unfold HRootLeHTarget at hH
  linarith

/-- Packaged original readout statement (finiteness + q ≤ 0 + target reading). -/
theorem paperCor312Readout_of_transport
    (hQ : QSourceLeQNorm (T := T) (I := I) (P := P))
    (hH : HRootLeHTarget (T := T) (I := I) (C3 := C3)) :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ ∧
      qPilotLogVolumeReading P ≤ 0 ∧
      qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3 := by
  refine ⟨paperReadout_thetaHull_finite C3, paperReadout_q_nonpos P, ?_⟩
  exact qPilotLogVolumeReading_le_thetaPilotHullLogVolumeReal_of_transport
    (T := T) (I := I) (C3 := C3) (P := P) hQ hH

def actualReadingTargetRows : List (String × String × String) :=
  [ ("middle arrow Q_norm ≤ H_root", "GREEN: actualPaperXiFTarget (actual root-hull containment, no S45/ratio/model)", "PROVED (unconditional)"),
    ("(R1) Q_src ≤ Q_norm", "same-q-witness + log n_def ≤ log n_norm (donor ratio ≥ 1) + weight/index match", "EXPLICIT ONE-WAY CONDITION"),
    ("(R3) H_root ≤ H_tgt", "root-hull (oneLabel branch + integer lattice) into thetaPilotHull C3 + Haar calibration raw=d·normalized+log μ(R)", "EXPLICIT ONE-WAY CONDITION"),
    ("qPilotLogVolumeReading ≤ thetaPilotHullLogVolumeReal", "R1 + green middle + R3 (no G2/G3 equalities, no normRatio=1)", "PROVED (conditional on R1,R3)"),
    ("(G1) PaperQPilotObjectActual inhabitant", "paper source obligation (P argument)", "EXTERNAL GAP") ]

theorem actualReadingTargetRows_length : actualReadingTargetRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ActualReadingTargetActual

end