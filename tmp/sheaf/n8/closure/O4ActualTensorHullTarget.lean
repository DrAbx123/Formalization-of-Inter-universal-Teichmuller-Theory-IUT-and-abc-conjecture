import tmp.sheaf.n8.closure.EtaLvSubmoduleSetActual
import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.P6Comparison

/-!
# O4 actual tensor hull target

Actual tensor hull log-volume `h_tensor` from the closed finite lattice volume
formula, the actual bound `Q ≤ h_tensor`, and the exact gap for equality with
the P6 source `ellOut`/Theta readout.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.O4ActualTensorHullTarget

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual
open LeanFormal.IUT.N8Closure.EtaLvSubmoduleSetActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct BigOperators

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev g0 : Kf X := gNonIntegral X

local instance : MeasurableSpace (E X) :=
  MeasurableSpace.map (tau X).symm (inferInstance : MeasurableSpace (Kf X))

noncomputable def hTensor (k : ℕ) : ℝ :=
  Real.log (((tensorHaar X (nnOrbitSubFinite X (g0 X) k)).toReal) /
    (((Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X))).toReal))

theorem hTensor_eq (k : ℕ) :
    hTensor X k = (k : ℝ) *
      (Module.finrank ℚ_[nativePrime X] (Kf X) : ℝ) *
        Real.log ‖g0 X‖ := by
  unfold hTensor
  rw [nnHullVolumeEqualityG0_actual X k]
  have hO0 : ((Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X))) ≠ 0 :=
    (EtaDistribHaarCharNormFormulaActual3.addHaar_O_pos X).ne'
  have hOfin : ((Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X))) ≠ ∞ :=
    (EtaDistribHaarCharNormFormulaActual3.addHaar_O_finite X).ne
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rw [mul_div_assoc]
  rw [div_self (by
    exact ENNReal.toReal_ne_zero.mpr ⟨hO0, hOfin⟩)]
  rw [mul_one]
  rw [show (((‖g0 X‖ ^ k) ^
      (Module.finrank ℚ_[nativePrime X] (Kf X) : ℕ) : ℝ)) =
      (‖g0 X‖ ^ k) ^ (Module.finrank ℚ_[nativePrime X] (Kf X)) by rfl]
  rw [Real.log_pow]
  rw [Real.log_pow]
  ring

theorem hTensor_nonneg (k : ℕ) : 0 ≤ hTensor X k := by
  rw [hTensor_eq]
  have hp1 : (1 : ℝ) < (nativePrime X : ℝ) :=
    by exact_mod_cast (Fact.out : Nat.Prime (nativePrime X)).one_lt
  have hg : ‖g0 X‖ = (nativePrime X : ℝ) := by
    change ‖(fPlaceP X)⁻¹‖ = (nativePrime X : ℝ)
    rw [norm_inv, fPlaceP_norm, inv_inv]
  have hlog : 0 < Real.log ‖g0 X‖ := by
    rw [hg]
    exact Real.log_pos hp1
  positivity

theorem Q_le_hTensor (k : ℕ) :
    qPilotSignedLog X ≤ hTensor X k := by
  have hQ : qPilotSignedLog X < 0 := qPilotSignedLog_neg X
  have hH : 0 ≤ hTensor X k := hTensor_nonneg X k
  linarith

/-- Exact gap: equality with the P6 source `ellOut`/Theta readout.  The source
object is not constructed and the normalization differs (tensor lattice
log-volume versus C6 normalized log-volume). -/
def HTensorEqEllOutTarget (J : SourceAllowedOutput X) : Prop :=
  hTensor X 0 = J.ellOut

def MissingHTensorEllOutAlignment : Prop :=
  ∃ J : SourceAllowedOutput X, HTensorEqEllOutTarget X J

end LeanFormal.IUT.N8Closure.O4ActualTensorHullTarget