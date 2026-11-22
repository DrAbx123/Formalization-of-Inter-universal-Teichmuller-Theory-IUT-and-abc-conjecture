import tmp.sheaf.n8.closure.EtaShellDepthQPilotAgreementActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellSignedDepthActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
open LeanFormal.IUT.N8Closure.EtaShellDepthQPilotAgreementActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem fShellUnitToAlgClUnit_one :
    fShellUnitToAlgClUnit X 1 = 1 := by
  unfold fShellUnitToAlgClUnit
  ext
  change fCompletionToPadicAlgCl X (1 : (fPlaceShell X).K) = 1
  exact map_one _

theorem unitShellDepth_one :
    unitShellDepth (nativePrime X) (1 : AlgClUnits X) = 0 := by
  unfold unitShellDepth
  rw [unitNormLogDegree_apply_one]
  simp

theorem shellDepth_one : shellDepth X 1 = 0 := by
  unfold shellDepth
  rw [fShellUnitToAlgClUnit_one, unitShellDepth_one]

/-- Decisive no-go: even the signed all-unit agreement is false.  The unit
`1` has depth `0`, while `qORegionLogVolume` is negative. -/
theorem etaShellSignedDepthQPilotAgreement_noGo :
    ¬ EtaShellSignedDepthQPilotAgreement X := by
  intro h
  have h1 := h 1
  have h0 : shellDepth X 1 = 0 := shellDepth_one X
  have hneg : qORegionLogVolume X < 0 := by
    rw [qORegionLogVolume_eq_qPilotSignedLog X]
    exact qPilotSignedLog_neg X
  linarith

/-! ## Corrected unit-dependent target -/

/-- Corrected target: there exists an actual shell unit whose depth is the
magnitude of the qO volume.  The all-units signed target is refuted above. -/
def EtaShellDepthMatchesQPilotMagnitude : Prop :=
  ∃ u : (fPlaceShell X).Units, shellDepth X u = -qORegionLogVolume X

def EtaShellDepthMatchesQPilotMagnitudeGap : Prop :=
  ¬ EtaShellDepthMatchesQPilotMagnitude X

/-! ## Exact missing equality -/

/- The missing depth/sign equality is unit-dependent: one must exhibit an
actual shell unit whose depth equals `-qORegionLogVolume` (equivalently
`-qPilotSignedLog`).  No arbitrary sign or all-unit agreement is assumed. -/
def EtaShellDepthQOSignEquation : Prop :=
  ∃ u : (fPlaceShell X).Units, shellDepth X u = -qPilotSignedLog X

end LeanFormal.IUT.N8Closure.EtaShellSignedDepthActual
