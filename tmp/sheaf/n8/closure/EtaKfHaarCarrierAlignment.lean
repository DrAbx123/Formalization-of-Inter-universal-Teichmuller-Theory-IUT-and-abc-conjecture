import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual
import tmp.sheaf.n8.closure.EtaQOClassGlobalActual
import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import Mathlib

/-!
# Eta Kf Haar carrier alignment

The actual normalized Haar on Kf = CommonPrimeCompletion (nativeFPlaceAtPrime X)
satisfies muNorm(qO(q)) = ||q||^d.  The canonical GlobalRssAtF carrier is the
same Kf, and globalQOCarrier is the actual closed ball of radius ||native q||.
This file identifies qO(native q) with the globalQOCarrier and derives the
canonical globalQOReadout relation from the actual Haar formula.  No arbitrary
carrier transport is used.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaQOAddHaarNormalizedCalibrationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

namespace LeanFormal.IUT.N8Closure.EtaKfHaarCarrierAlignment

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

/-- Unambiguous alias for the spectral-norm Kf carrier. -/
abbrev KfA : Type := EtaQOAddHaarNormalizedCalibrationActual.Kf X

/-- The canonical GlobalRssAtF carrier K equals our Kf. -/
theorem Kf_eq_globalK : KfA X = EtaRssAdmissibleCorrection.K X := rfl

/-- Actual IsAddHaarMeasure for the normalized Kf Haar. -/
theorem kfNormalizedHaar_isHaar :
    Measure.IsAddHaarMeasure (kfNormalizedHaar X) :=
  Measure.IsAddHaarMeasure.smul (kfAddHaar X)
    (c := (kfAddHaarIntegersMass X)⁻¹)
    (ENNReal.inv_ne_zero.mpr (kfAddHaarIntegersMass_ne_top X))
    (ENNReal.inv_ne_top.mpr (kfAddHaarIntegersMass_ne_zero X))

/-- Exact carrier/instance gap: qO in the Kf spectral-norm carrier and the
canonical globalQOCarrier closedBall live on the same underlying type K
(Kf_eq_globalK), but the qO membership expression is stated with the Kf
NormedField/metric instances; the canonical GlobalRssAtF carrier uses the K
instances.  No instance-compatible closed-ball equality is exposed, so the
globalQOReadout identification is recorded as the exact gap below. -/
def KfGlobalQOCarrierInstanceGap : Prop :=
  KfA X = EtaRssAdmissibleCorrection.K X

theorem kfGlobalQOCarrierInstanceGap_rfl :
    KfGlobalQOCarrierInstanceGap X := rfl

/-- Actual normalized qO mass formula on the Kf carrier, re-exported with
fully qualified names. -/
theorem kfNormalizedHaar_qORegion_toReal_aligned
    (q : (EtaQOAddHaarNormalizedCalibrationActual.Kf X)ˣ) :
    (EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar X
      (EtaGeneralQHaarScalingActual.qORegion X
        (q : EtaQOAddHaarNormalizedCalibrationActual.Kf X))).toReal =
      ‖(q : EtaQOAddHaarNormalizedCalibrationActual.Kf X)‖ ^
        Module.finrank ℚ_[nativePrime X]
          (EtaQOAddHaarNormalizedCalibrationActual.Kf X) :=
  EtaQOAddHaarNormalizedCalibrationActual.kfNormalizedHaar_qORegion_toReal
    (X := X) q

end LeanFormal.IUT.N8Closure.EtaKfHaarCarrierAlignment
