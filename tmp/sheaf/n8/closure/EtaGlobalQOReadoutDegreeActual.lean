import tmp.sheaf.n8.closure.EtaGlobalQODegreeCorrectedAlignment
import tmp.sheaf.n8.closure.EtaQBaseImageCondition
import tmp.sheaf.n8.closure.EtaQOClassReadoutDegreeCorrected
import Mathlib

/-!
# Eta global qO readout degree actual

The degree-corrected carrier correctedGlobalQOCarrier is exactly qORegion under
the native norm power relation.  Therefore its kfNormalizedHaar log readout is

  correctedGlobalQOReadout = d * log ||q_normalized||.

The corrected normalized readout (multiplying by relDegree) equals
qPilotSignedLog under QBaseImageCondition (which supplies the power relation)
and nonzero d.  No arbitrary normalization is used.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQBaseImageCondition
open LeanFormal.IUT.N8Closure.EtaQOClassReadoutDegreeCorrected
open LeanFormal.IUT.N8Closure.EtaGlobalQODegreeCorrectedAlignment
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- The spectral-norm Kf carrier. -/
abbrev KF (X : N8NativeInput l) : Type := EtaGeneralQHaarScalingActual.Kf X

/-- Corrected global qO readout: log of the normalized Haar mass of the
degree-corrected carrier. -/
noncomputable def correctedGlobalQOReadout : ℝ :=
  Real.log (kfNormalizedHaar X (correctedGlobalQOCarrier X)).toReal

/-- Readout of the corrected carrier is d * log of the normalized q norm. -/
theorem correctedGlobalQOReadout_eq_dim_mul_log
    (hpow : NativeNormPowerRelation X)
    (hrel : (relDegree X : ℝ) ≠ 0) :
    correctedGlobalQOReadout X =
      (Module.finrank ℚ_[nativePrime X] (KF X) : ℝ) *
        Real.log ‖((nativeQUnitKf X) : KF X)‖ := by
  unfold correctedGlobalQOReadout
  rw [correctedGlobalQOCarrier_eq_qORegion (X := X) hpow hrel]
  exact kfNormalizedHaar_qORegion_log (X := X) (nativeQUnitKf X)

/-- Degree-corrected normalized readout, multiplying by relDegree. -/
noncomputable def correctedNormalizedGlobalQOReadout : ℝ :=
  correctedGlobalQOReadout X * (relDegree X : ℝ) /
    (Module.finrank ℚ_[nativePrime X] (KF X) : ℝ)

/-- The corrected normalized readout equals qPilotSignedLog under the source
base-image condition. -/
theorem correctedNormalizedGlobalQOReadout_eq_qPilot
    (B : QBaseImageCondition X)
    (hrel : (relDegree X : ℝ) ≠ 0)
    (hd : (Module.finrank ℚ_[nativePrime X] (KF X) : ℝ) ≠ 0) :
    correctedNormalizedGlobalQOReadout X = qPilotSignedLog X := by
  have hpow : NativeNormPowerRelation X :=
    nativeNormPowerRelation_of_baseImageCondition (X := X) B
  have hread := correctedGlobalQOReadout_eq_dim_mul_log (X := X) hpow hrel
  have hq : qPilotSignedLog X =
      (relDegree X : ℝ) * Real.log ‖((nativeQUnitKf X) : KF X)‖ := by
    calc
      qPilotSignedLog X = Real.log ‖nativeQVal X‖ := qPilot_eq_log_native X
      _ = Real.log (‖normalizedQVal X‖ ^ relDegree X) := by rw [hpow]
      _ = (relDegree X : ℝ) * Real.log ‖normalizedQVal X‖ :=
        Real.log_pow (‖normalizedQVal X‖) (relDegree X)
      _ = (relDegree X : ℝ) * Real.log ‖((nativeQUnitKf X) : KF X)‖ := rfl
  unfold correctedNormalizedGlobalQOReadout
  rw [hread, hq]
  field_simp [hd]

/-- Exact gap for the corrected normalized qPilot readout: the source
base-image condition is not derivable internally. -/
def CorrectedNormalizedGlobalQOReadoutSourceGap : Prop :=
  QBaseImageCondition X

end LeanFormal.IUT.N8Closure.EtaGlobalQOReadoutDegreeActual
