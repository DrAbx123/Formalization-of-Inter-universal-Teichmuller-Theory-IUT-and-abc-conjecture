import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import tmp.sheaf.xif.paper.Node09P5NormalizedRegionActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.Mzk1P4JqLatticeActual
import tmp.sheaf.xif.paper.Mzk1QVMultiplicityBridgeActual
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.NativeBadLiftActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Node09P5NormalizedRegionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QVMultiplicityBridgeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual

namespace LeanFormal.IUT.XiFPaper.Node09P5ReadingBridgeActual

/-- Per-b actual normalized qVFam volume equals the negative classical local
log magnitude plus the actual norm-ratio correction. -/
theorem qVFamNormalizedQPilotVolume_eq_neg_localLog_add_ratio
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))
    [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))]
    [MeasurableSpace (qVFamTensorBlock T b)] [BorelSpace (qVFamTensorBlock T b)] :
    qVFamNormalizedQPilotVolume T b =
      -localLogMagnitude (qVFamily T b) + Real.log (qVFamNormRatio T b) := by
  rw [qVFamNormalizedQPilotVolume_eq]
  have h := qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio (T := T) (b := b)
  linarith

/-- The sum of actual local log magnitudes is the negative realified q-pilot
log-volume. -/
theorem sum_localLogMagnitude_eq_neg_qPilot
    {l : PrimeGeFive} (X : N8NativeInput l)
    [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S))] :
    (∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b)) =
      -qPilotRealifiedLogVolume X := by
  rw [qPilotRealifiedLogVolume_eq]
  simp only [neg_neg]
  apply Finset.sum_congr rfl
  intro b _
  rw [localLogMagnitude_eq_order_mul_log]
  rw [qVEffectiveMultiplicity_eq_order_mul_localResidueDegree]
  have hres : residueNormBase ((LeanFormal.IUT.N8Closure.nativeBadLift X.S).lift b) =
      residueNormBase (b.1) ^
        localResidueDegree (k := X.S.arithmetic.Fmod) ((LeanFormal.IUT.N8Closure.nativeBadLift X.S).lift b) := by
    rw [residueNormBase_eq_lower_pow (k := X.S.arithmetic.Fmod)]
    rw [(LeanFormal.IUT.N8Closure.nativeBadLift X.S).lift_comap b]
  rw [hres, Real.log_pow]
  push_cast
  ring

/-- Actual global reading bridge: the sum of per-b normalized qVFam volumes is
the realified q-pilot log-volume plus the explicit norm-ratio correction. -/
theorem sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio
    {l : PrimeGeFive} (X : N8NativeInput l)
    [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S))]
    [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      MeasurableSpace (qVFamTensorBlock X.S b)]
    [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
      BorelSpace (qVFamTensorBlock X.S b)] :
    (∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
        qVFamNormalizedQPilotVolume X.S b) =
      qPilotRealifiedLogVolume X +
        ∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
          Real.log (qVFamNormRatio X.S b) := by
  rw [Finset.sum_congr rfl (fun b _ =>
    qVFamNormalizedQPilotVolume_eq_neg_localLog_add_ratio X.S b)]
  rw [Finset.sum_add_distrib]
  rw [show (∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
        -localLogMagnitude (qVFamily X.S b)) =
      -(∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b)) by
    rw [Finset.sum_neg_distrib]]
  rw [sum_localLogMagnitude_eq_neg_qPilot X]
  ring

#print axioms qVFamNormalizedQPilotVolume_eq_neg_localLog_add_ratio
#print axioms sum_localLogMagnitude_eq_neg_qPilot
#print axioms sum_qVFamNormalizedQPilotVolume_eq_qPilot_add_ratio

end LeanFormal.IUT.XiFPaper.Node09P5ReadingBridgeActual
end