import tmp.sheaf.n8.closure.EtaRootSystemReadoutScalingPositiveActual
import tmp.sheaf.n8.closure.EtaVaryingCalibrationQOActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellActionReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScaling
open LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScalingPositiveActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Explicit readout formula from positive scaling: the logMap of the
partial action image is the original logMap divided by `m+1`. -/
theorem partialShellAction_logMap_div (m : Nat) (hm : m ≠ 0)
    (u : (fPlaceShell X).Units) (h : u ∈ goodShellUnit X m 1) :
    ((fPlaceShell X).logMap (partialShellAction X m 1 u h)).toAdd =
      ((fPlaceShell X).logMap u).toAdd / ((m + 1 : Nat) : (fPlaceShell X).K) := by
  have hscaling := partialReadoutScalingPositive X m hm u h
  have hcast : ((m + 1 : Nat) : (fPlaceShell X).K) *
      ((fPlaceShell X).logMap (partialShellAction X m 1 u h)).toAdd =
      ((fPlaceShell X).logMap u).toAdd := by
    simpa [nsmul_eq_mul] using hscaling
  have hne : ((m + 1 : Nat) : (fPlaceShell X).K) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  rw [eq_div_iff hne]
  simpa [mul_comm] using hcast

/-- Actual qPilot/qO volume identity: qORegionLogVolume equals the native
q-pilot signed log. -/
theorem qPilotVolumeActual :
    qORegionLogVolume X = qPilotSignedLog X :=
  qORegionLogVolume_eq_qPilotSignedLog X

/-! ## Exact normalization gap -/

/- The scaling formula lives in the F-completion `K`, while `qPilotSignedLog`
is the real log-volume of the actual qO region.  A normalization map from
F-shell log coordinates to the qO real readout is not present in production.
The structure below is the exact normalization target: it is not inhabited
by an arbitrary readout. -/
structure EtaShellQPilotNormalization (X : N8NativeInput l) where
  normLog : (fPlaceShell X).K → ℝ
  normLog_zero : normLog 0 = 0
  normLog_shell : ∀ u : (fPlaceShell X).Units,
    normLog ((fPlaceShell X).logMap u).toAdd = qORegionLogVolume X
  normLog_scaling : ∀ (m : Nat) (_hm : m ≠ 0) (x : (fPlaceShell X).K),
    normLog (x / ((m + 1 : Nat) : (fPlaceShell X).K)) =
      normLog x / ((m + 1 : Nat) : ℝ)

def EtaShellQPilotNormalizationGap : Prop :=
  ¬ Nonempty (EtaShellQPilotNormalization X)

end LeanFormal.IUT.N8Closure.EtaShellActionReadoutActual
