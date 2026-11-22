/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotFromSourceLActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import Mathlib.Tactic
/-! # P0: S3137 readouts on the L-side actual record (no old empty C3) -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open MeasureTheory
universe ua upi umon ui
variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable (C3L : SourcePilotRegionDataL (I := I))
noncomputable def qPilotLogVolumeReadingL : Real :=
  OrigXiFSourceLQScalar (I := I) C3L
theorem qPilotLogVolumeReadingL_eq_neg_abs :
    qPilotLogVolumeReadingL C3L = -|Real.log ‖C3L.q.q‖| := by
  unfold qPilotLogVolumeReadingL
  rw [OrigXiFSourceLQScalar_eq_log_norm]
  have hneg : Real.log ‖C3L.q.q‖ < 0 :=
    OrigXiFSourceLQScalar_neg (I := I) C3L
  rw [abs_of_neg hneg]
  ring
theorem qPilotLogVolumeReadingL_eq_LQScalar :
    qPilotLogVolumeReadingL C3L = OrigXiFSourceLQScalar (I := I) C3L := rfl
theorem qPilotLogVolumeReadingL_nonpos :
    qPilotLogVolumeReadingL C3L ≤ 0 := by
  unfold qPilotLogVolumeReadingL
  exact (OrigXiFSourceLQScalar_neg (I := I) C3L).le
noncomputable def thetaPilotHullLogVolumeRealL : Real :=
  Real.log ((actualC3LogShellTensorHaarL (I := I) C3L)
    (actualC3LogShellTensorRegionL (I := I) C3L)).toReal
def LPaper312Statement (C3L : SourcePilotRegionDataL (I := I))
    (D : SourcePilotRegionDataL (I := I)) : Prop :=
  qPilotLogVolumeReadingL D ≤ thetaPilotHullLogVolumeRealL C3L
def rows : List String := ["qPilotLogVolumeReadingL = -|log q|", "thetaPilotHullLogVolumeRealL = log actual L Haar region", "LPaper312Statement (P0 target, not proved)", "no old C3 / no IsEmpty"]
theorem rows_length : rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
end