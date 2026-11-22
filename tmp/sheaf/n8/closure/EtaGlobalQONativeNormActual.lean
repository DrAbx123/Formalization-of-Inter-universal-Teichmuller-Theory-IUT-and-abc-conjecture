import tmp.sheaf.n8.closure.EtaKfClosedBallEqQORegion
import tmp.sheaf.n8.closure.EtaFPlaceNormAgreementActualAttempt
import tmp.sheaf.n8.closure.EtaQORegionMassNormFromScaling
import Mathlib

/-!
# Eta global qO native norm actual

The Kf closed-ball/qO identity is proved in the spectral norm.  The canonical
globalQOCarrier uses the native q with the QCompletion/default norm.  The exact
norm agreement is FPlaceNormAgreement.  Under that agreement the Kf closed ball
of the native radius is exactly the qO region of the normalized q unit.  The
norm power relation and the relative degree are the exact gap: agreement forces
relDegree = 1.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormAgreementActualAttempt
open LeanFormal.IUT.N8Closure.EtaQORegionMassNormFromScaling
open LeanFormal.IUT.N8Closure.EtaFPlaceLogNormAgreementActual
open LeanFormal.IUT.N8Closure.EtaKfClosedBallEqQORegion
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaGlobalQONativeNormActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Under the exact native/normalized norm agreement, the Kf closed ball of the
native radius is exactly the qO region of the normalized q unit. -/
theorem kf_closedBall_globalQO_eq_qORegion_of_normAgreement
    (h : FPlaceNormAgreement (X := X)) :
    Metric.closedBall (0 : EtaGeneralQHaarScalingActual.Kf X)
        ‖(C9QPilotRegion.nativeQ X).q‖ =
      qORegion X
        ((nativeQUnitKf X) : EtaGeneralQHaarScalingActual.Kf X) := by
  rw [kf_qORegion_eq_closedBall (X := X) (nativeQUnitKf X)]
  congr 1
  exact h.symm

/-- Exact norm-power/degree no-go: under the native/normalized power relation,
norm agreement holds iff the relative degree is 1. -/
theorem fPlaceNormAgreement_iff_degree_one_of_power
    (hpow : NativeNormPowerRelation X)
    (hne0 : ‖normalizedQVal X‖ ≠ 0)
    (hne1 : ‖normalizedQVal X‖ ≠ 1) :
    FPlaceNormAgreement (X := X) ↔ relDegree X = 1 :=
  EtaFPlaceNormAgreementActualAttempt.fPlaceNormAgreement_iff_degree_one_of_power
    (X := X) hpow hne0 hne1

/-- Conditional carrier alignment from the relative degree being one. -/
theorem kf_closedBall_globalQO_eq_qORegion_of_degree_one
    (hpow : NativeNormPowerRelation X)
    (hne0 : ‖normalizedQVal X‖ ≠ 0)
    (hne1 : ‖normalizedQVal X‖ ≠ 1)
    (hdeg : relDegree X = 1) :
    Metric.closedBall (0 : EtaGeneralQHaarScalingActual.Kf X)
        ‖(C9QPilotRegion.nativeQ X).q‖ =
      qORegion X
        ((nativeQUnitKf X) : EtaGeneralQHaarScalingActual.Kf X) :=
  kf_closedBall_globalQO_eq_qORegion_of_normAgreement (X := X)
    ((fPlaceNormAgreement_iff_degree_one_of_power (X := X) hpow hne0 hne1).mpr hdeg)

/-- Exact norm/type gap for the globalQOCarrier alignment: the norm agreement
is not available unconditionally; it requires the power relation and degree one.
No arbitrary carrier transport is introduced. -/
def GlobalQOCarrierNormAlignmentGap : Prop :=
  FPlaceNormAgreement (X := X)

end LeanFormal.IUT.N8Closure.EtaGlobalQONativeNormActual
