import tmp.sheaf.n8.closure.EtaShellQUnitCandidateActual
import tmp.sheaf.n8.closure.EtaRootSystemReadoutScalingPositiveActual
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer

set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQUnitAlgClDepthActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaShellQUnitCandidateActual
open LeanFormal.IUT.N8Closure.EtaShellDepthScalingActual
open LeanFormal.IUT.N8Closure.EtaShellSignedDepthActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaQActual
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : NormedField (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionNormedField
    (place := nativeFPlaceAtPrime X)
local instance : IsUltrametricDist (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionUltrametric
    (place := nativeFPlaceAtPrime X)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

noncomputable def qUnitK : (fPlaceShell X).K :=
  (etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)

theorem qUnitK_ne_zero : qUnitK X ≠ 0 := by
  simpa [qUnitK] using Units.ne_zero (etaQUnit X)

/-- Actual qUnit image in the common algebraic-closure unit group, via the
actual F-completion embedding (not an arbitrary unit). -/
noncomputable def qUnitAlgCl : AlgClUnits X :=
  Units.mk0 (fCompletionToPadicAlgCl X (qUnitK X)) (by
    intro hzero
    have h0 : (fCompletionToPadicAlgCl X) (qUnitK X) =
        (fCompletionToPadicAlgCl X) 0 := by
      simpa using hzero
    exact ((fCompletionToPadicAlgCl X).injective.ne (qUnitK_ne_zero X)) h0)

/-- Actual calibration etaQScalar = qPilotSignedLog. -/
theorem etaQScalar_eq_qPilot : etaQScalar X = qPilotSignedLog X := by
  unfold etaQScalar qPilotSignedLog ArithmeticQPilotLogVolume.localSignedLog
  change Multiplicative.toAdd (Multiplicative.ofAdd
    (Real.log ‖((Units.mk0 (nativeQActual X).q (nativeQActual X).q_ne_zero) :
      Completion (nativeFPlaceOverBad X))‖)) = Real.log ‖(nativeQActual X).q‖
  rw [Units.val_mk0]
  rfl

/-- Exact missing norm preservation on the qUnit: the actual F-completion
embedding must preserve its norm. -/
def EtaQUnitEmbeddingNormLaw : Prop :=
  ‖(qUnitAlgCl X : PadicAlgCl (nativePrime X))‖ =
    ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖

/-- Conditional actual depth: given the embedding norm law, the production
unitShellDepth of the qUnit AlgCl image is `-qPilotSignedLog`. -/
theorem qUnitAlgCl_depth_of_normLaw
    (hnorm : EtaQUnitEmbeddingNormLaw X) :
    unitShellDepth (nativePrime X) (qUnitAlgCl X) = -qPilotSignedLog X := by
  have hcal : etaQScalar X = qPilotSignedLog X := etaQScalar_eq_qPilot X
  have hnorm' : ‖(qUnitAlgCl X : PadicAlgCl (nativePrime X))‖ =
      ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖ := hnorm
  unfold unitShellDepth
  rw [show unitNormLogDegree (AlgebraicClosure ℚ_[nativePrime X]) (qUnitAlgCl X) =
      Multiplicative.ofAdd (Real.log ‖(qUnitAlgCl X : PadicAlgCl (nativePrime X))‖) from rfl]
  rw [hnorm']
  have hq : ((etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)) ≠ 0 := Units.ne_zero (etaQUnit X)
  have hlogneg : Real.log ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖ < 0 :=
    Real.log_neg (norm_pos_iff.mpr hq) (nativeQUnit_thm_norm_lt_one X)
  rw [show (Multiplicative.toAdd (Multiplicative.ofAdd
      (Real.log ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖))) =
      Real.log ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖ from rfl]
  rw [max_eq_right (by linarith : 0 ≤ -Real.log ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖)]
  have hlog : Real.log ‖(etaQUnit X : EtaShellQUnitCandidateActual.QCompletion X)‖ = qPilotSignedLog X := by
    rw [← hcal]
    rfl
  linarith

def EtaQUnitEmbeddingNormLawGap : Prop :=
  ¬ EtaQUnitEmbeddingNormLaw X

end LeanFormal.IUT.N8Closure.EtaQUnitAlgClDepthActual
