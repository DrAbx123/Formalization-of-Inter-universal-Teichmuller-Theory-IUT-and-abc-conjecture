import tmp.sheaf.xif.paper.Mzk1S3137LReadoutActual
import tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
import tmp.sheaf.xif.paper.OrigXiFPaperQPilotFromSourceLActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
/-! CONSUMER RE-EXPORT — re-exports an existing theorem; not a new proof. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.Mzk1P0LS3137LFinalActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotFromSourceLActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1S3137LReadoutActual
open MeasureTheory


variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable (C3L : SourcePilotRegionDataL (I := I))
include I C3L
theorem qReading_final :
    qPilotLogVolumeReadingL C3L = -|Real.log ‖C3L.q.q‖| :=
  qPilotLogVolumeReadingL_eq_neg_abs C3L
theorem qReading_nonpos_final : qPilotLogVolumeReadingL C3L ≤ 0 := by
  rw [qReading_final C3L]
  exact neg_nonpos.mpr (abs_nonneg _)
end LeanFormal.IUT.XiFPaper.Mzk1P0LS3137LFinalActual