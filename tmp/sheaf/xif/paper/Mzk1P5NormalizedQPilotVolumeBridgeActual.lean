/- P5 reading identification: global weighted sum bridge between per-b
qVFamNormalizedQPilotVolume and qPilotRealifiedLogVolume (or explicit
norm-ratio correction).  Uses actual jqIndex/weightedReadout; no
PaperKummerReading fields. -/
import tmp.sheaf.xif.paper.Node09P5NormalizedRegionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1P4WeightedReadingClosureActual
import tmp.sheaf.xif.paper.Mzk1P4P5QThetaReadingIntegrationActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadingClosureActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P4P5QThetaReadingIntegrationActual

variable {l : PrimeGeFive}

/-- Single-place normalized qVFam volume in terms of the classical local log
magnitude plus the actual normalized/default norm-ratio log. -/
theorem qVFamNormalizedQPilotVolume_eq_neg_localLogMagnitude_add_log_ratio
    (T : SourceNativeInitialThetaData.{0} l) [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection T))]
    (b : Bad (LeanFormal.IUT.nativePlaceSelection T))
    [MeasurableSpace (qVFamTensorBlock T b)] [BorelSpace (qVFamTensorBlock T b)] :
    qVFamNormalizedQPilotVolume T b =
      -LeanFormal.IUT.ArithmeticQPilotLogVolume.localLogMagnitude (qVFamily T b) + Real.log (qVFamNormRatio T b) := by
  rw [qVFamNormalizedQPilotVolume_eq]
  rw [← qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio T b]
  ring

/-- The sum of the actual qVFamily local magnitudes is exactly the negative of
the realified q-pilot log-volume. -/
theorem sum_localLogMagnitude_eq_neg_qPilot
    (X : N8NativeInput l) [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)] :
    (∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
        LeanFormal.IUT.ArithmeticQPilotLogVolume.localLogMagnitude (qVFamily X.S b)) =
      -qPilotRealifiedLogVolume X := by
  rw [qPilotRealifiedLogVolume_eq_neg_sum_localLogMagnitude X]
  ring

/-- Summed P5 reading identification: the per-b normalized qVFam volume sum is
the realified q-pilot scalar plus the exact norm-ratio correction. -/
theorem sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio
    (X : N8NativeInput l) [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)] :
    (∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
        qVFamNormalizedQPilotVolume X.S b) =
      qPilotRealifiedLogVolume X +
        ∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
          Real.log (qVFamNormRatio X.S b) := by
  rw [Finset.sum_congr rfl (fun b _ =>
    qVFamNormalizedQPilotVolume_eq_neg_localLogMagnitude_add_log_ratio X.S b)]
  rw [Finset.sum_add_distrib]
  rw [show (∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
        -LeanFormal.IUT.ArithmeticQPilotLogVolume.localLogMagnitude (qVFamily X.S b)) =
      -(∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
        LeanFormal.IUT.ArithmeticQPilotLogVolume.localLogMagnitude (qVFamily X.S b)) by
    rw [Finset.sum_neg_distrib]]
  rw [sum_localLogMagnitude_eq_neg_qPilot X]
  ring

/-- Global weighted sum bridge via actual weightedReadout: the per-b qVFam
normalized volume sum equals the weight-1 bad-side readout plus the actual
norm-ratio correction. -/
theorem sum_qVFamNormalizedQPilotVolume_eq_weightedReadout_add_ratio
    (X : N8NativeInput l) [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)] :
    (∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
        qVFamNormalizedQPilotVolume X.S b) =
      weightedReadout X (fun _ => 1) +
        ∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
          Real.log (qVFamNormRatio X.S b) := by
  rw [sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio X]
  rw [weightedReadout_one_eq_logVolume X]

/-- Dually, the sum equals the negative jqIndex log plus the exact correction. -/
theorem sum_qVFamNormalizedQPilotVolume_eq_neg_log_jqIndex_add_ratio
    (X : N8NativeInput l) [Fintype (Bad (LeanFormal.IUT.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S), BorelSpace (qVFamTensorBlock X.S b)] :
    (∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
        qVFamNormalizedQPilotVolume X.S b) =
      -Real.log (jqIndex (X := X) : Real) +
        ∑ b : Bad (LeanFormal.IUT.nativePlaceSelection X.S),
          Real.log (qVFamNormRatio X.S b) := by
  rw [sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio X]
  rw [p4_qPilot_eq_neg_log_jqIndex X]

#print axioms qVFamNormalizedQPilotVolume_eq_neg_localLogMagnitude_add_log_ratio
#print axioms sum_localLogMagnitude_eq_neg_qPilot
#print axioms sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio
#print axioms sum_qVFamNormalizedQPilotVolume_eq_weightedReadout_add_ratio
#print axioms sum_qVFamNormalizedQPilotVolume_eq_neg_log_jqIndex_add_ratio

end
