import tmp.sheaf.n8.closure.EtaShellQPilotNormalizationActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaShellNormLogScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaShellQPilotNormalizationActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : NormedField (fPlaceShell X).K :=
  NumberFieldFinitePlace.commonPrimeCompletionNormedField
    (place := nativeFPlaceAtPrime X)

/-- Exact integer norm/log equality needed by the target scaling: the real log
norm of the integer `m+1` must vanish.  This is the missing normalization
equation; the true norm law is affine (norm of a quotient subtracts the log
norm of the denominator), not multiplicative division. -/
def EtaIntegerNormLogLaw : Prop :=
  ∀ (m : Nat) (_hm : m ≠ 0),
    Real.log ‖((m + 1 : Nat) : (fPlaceShell X).K)‖ = 0

/-- Exact scaling gap. -/
def EtaShellNormLogScalingGap : Prop :=
  ¬ EtaShellNormLogScaling X

/-- Exact agreement gap. -/
def EtaShellNormLogAgreementGap : Prop :=
  ¬ EtaShellNormLogAgreement X

end LeanFormal.IUT.N8Closure.EtaShellNormLogScalingActual
