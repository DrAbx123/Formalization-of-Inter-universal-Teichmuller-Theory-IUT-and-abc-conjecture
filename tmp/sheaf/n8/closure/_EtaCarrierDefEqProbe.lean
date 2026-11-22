import tmp.sheaf.n8.closure.EtaQIndependentAttempt
import tmp.sheaf.n8.closure.C3TensorTargetCorrection
import tmp.sheaf.n8.closure.EtaIntegralStructureAtSelectedPlace
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionPacketLogShell

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaCarrierDefEqProbe

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.EtaQIndependentAttempt
open LeanFormal.IUT.N8Closure.EtaIntegralStructureAtSelectedPlaceRoute
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection

variable {l : PrimeGeFive} (X : N8NativeInput l)

example : CommonPrimeCompletion (nativeFPlaceAtPrime X) = NativeQCarrier X := rfl

noncomputable def auditRingEquiv :
    CommonPrimeCompletion (nativeFPlaceAtPrime X) ≃+* NativeQCarrier X :=
  commonPrimeCompletionActualRingEquiv (nativeFPlaceAtPrime X)

example : SelectedCompletion X =
    CommonPrimeCompletion (selectedBadPlaceAtPrime X) := rfl

end LeanFormal.IUT.N8Closure.EtaCarrierDefEqProbe