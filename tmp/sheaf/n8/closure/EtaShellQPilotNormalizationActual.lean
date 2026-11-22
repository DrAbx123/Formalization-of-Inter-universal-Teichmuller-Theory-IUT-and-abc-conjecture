import tmp.sheaf.n8.closure.EtaShellActionReadoutActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellQPilotNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScaling
open LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScalingPositiveActual
open LeanFormal.IUT.N8Closure.EtaShellActionReadoutActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : NormedField (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionNormedField
    (place := nativeFPlaceAtPrime X)

/-- Actual candidate norm-log on the shell carrier: normalized negative p-adic
log of the norm.  It is defined from the actual shell K norm, not arbitrary. -/
noncomputable def shellNormLog (x : (fPlaceShell X).K) : ℝ :=
  - Real.log ‖x‖ / Real.log (nativePrime X : ℝ)

theorem shellNormLog_zero : shellNormLog X 0 = 0 := by
  rw [shellNormLog]
  have h0 : ‖(0 : (fPlaceShell X).K)‖ = 0 := norm_zero
  rw [h0, Real.log_zero]
  simp

/-! ## Exact agreement/scaling equations -/

/-- Missing norm/log equality: on shell `logMap` values the candidate must
agree with the actual qO region log-volume. -/
def EtaShellNormLogAgreement : Prop :=
  ∀ u : (fPlaceShell X).Units,
    shellNormLog X ((fPlaceShell X).logMap u).toAdd = qORegionLogVolume X

/-- Missing norm/log scaling equality for division by `m+1`. -/
def EtaShellNormLogScaling : Prop :=
  ∀ (m : Nat) (_hm : m ≠ 0) (x : (fPlaceShell X).K),
    shellNormLog X (x / ((m + 1 : Nat) : (fPlaceShell X).K)) =
      shellNormLog X x / ((m + 1 : Nat) : ℝ)

/-- Conditional actual normalization: the explicit candidate `shellNormLog`
satisfies zero, and agreement/scaling are the two exact missing equations. -/
def etaShellQPilotNormalization_of_equations
    (hagr : EtaShellNormLogAgreement X)
    (hscal : EtaShellNormLogScaling X) :
    EtaShellQPilotNormalization X where
  normLog := shellNormLog X
  normLog_zero := shellNormLog_zero X
  normLog_shell := hagr
  normLog_scaling := hscal

/-! ## Exact gap -/

/- The two equations above are the precise missing norm/log facts: agreement
of the shell norm-log with `qORegionLogVolume` on `logMap` values, and the
normalization/scaling of division by `m+1`.  Neither is assumed. -/
def EtaShellQPilotNormalizationGapActual : Prop :=
  ¬ (EtaShellNormLogAgreement X ∧ EtaShellNormLogScaling X)

end LeanFormal.IUT.N8Closure.EtaShellQPilotNormalizationActual
