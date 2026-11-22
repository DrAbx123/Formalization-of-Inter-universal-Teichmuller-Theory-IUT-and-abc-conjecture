import tmp.sheaf.n8.closure.EtaShellDepthScalingActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellDepthQPilotAgreementActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Decisive no-go: the depth readout is nonnegative, while the actual qO
log-volume is the negative qPilotSignedLog.  Hence `shellDepth u` cannot
equal `qORegionLogVolume` for all shell units. -/
theorem etaShellDepthQPilotAgreement_noGo :
    ¬ EtaShellDepthQPilotAgreement X := by
  intro h
  have h1 := h 1
  have hnonneg : 0 ≤ shellDepth X 1 := by
    unfold shellDepth
    exact unitShellDepth_nonneg (nativePrime X) (fShellUnitToAlgClUnit X 1)
  have hneg : qORegionLogVolume X < 0 := by
    rw [qORegionLogVolume_eq_qPilotSignedLog X]
    exact qPilotSignedLog_neg X
  linarith

/-! ## Corrected signed target -/

/-- Corrected signed agreement: the negative depth equals the qO log-volume.
The sign correction is forced by the no-go above. -/
def EtaShellSignedDepthQPilotAgreement : Prop :=
  ∀ u : (fPlaceShell X).Units, -shellDepth X u = qORegionLogVolume X

def EtaShellSignedDepthQPilotAgreementGap : Prop :=
  ¬ EtaShellSignedDepthQPilotAgreement X

/-! ## Exact missing equality -/

/- The missing norm/log equality is the signed depth identity above: the
unit-shell depth must be the negative of `qORegionLogVolume` (equivalently
`-qPilotSignedLog`) on shell units.  No arbitrary agreement is assumed. -/
def EtaShellDepthMagnitudeEqQPilot : Prop :=
  ∀ u : (fPlaceShell X).Units, shellDepth X u = -qORegionLogVolume X

end LeanFormal.IUT.N8Closure.EtaShellDepthQPilotAgreementActual
