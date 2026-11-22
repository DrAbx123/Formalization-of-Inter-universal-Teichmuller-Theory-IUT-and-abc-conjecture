import tmp.sheaf.n8.closure.EtaRootSystemCommutationAttempt
import LeanFormal.IUT.IUTII.Kummer.VerticalLogKummerOrderedLayer

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScaling

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaPartialReadoutActual
open LeanFormal.IUT.N8Closure.EtaPartialReadoutPositiveAttempt
open LeanFormal.IUT.N8Closure.EtaRootSystemCommutationAttempt
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem rootSystemPowRoot_one (x : AlgClUnits X) :
    rootSystemPowRoot (nativePrime X) 1 x = x := by
  have h := rootSystemPowRoot_pow (nativePrime X) 1 one_ne_zero x
  simpa using h

/-! ## Corrected scaling readout -/

/-- Corrected readout on the partial-action good domain: the `(m+1)`-fold
log of the action image equals the original log (scaling), NOT invariance. -/
def EtaPartialReadoutScaling (m : Nat) : Prop :=
  ∀ (u : (fPlaceShell X).Units) (h : u ∈ goodShellUnit X m 1),
    ((m + 1 : Nat) •
      ((fPlaceShell X).logMap (partialShellAction X m 1 u h)).toAdd) =
    ((fPlaceShell X).logMap u).toAdd

theorem partialReadoutScaling_zero :
    EtaPartialReadoutScaling X 0 := by
  intro u h
  have hv := partialShellAction_spec X 0 1 u h
  have hroot : layerUnitAction X 0 1 (fShellUnitToAlgClUnit X u) =
      fShellUnitToAlgClUnit X u := by
    rw [layerUnitAction_one]
    simpa using rootSystemPowRoot_one (X := X) (fShellUnitToAlgClUnit X u)
  have hvu : partialShellAction X 0 1 u h = u :=
    fShellUnitToAlgClUnit_injective X (by rw [hv, hroot])
  simpa [hvu]

/-! ## Exact positive-step gap -/

/-- Exact positive-step scaling target. -/
def EtaPartialReadoutScalingPositive : Prop :=
  ∀ (m : Nat), m ≠ 0 → EtaPartialReadoutScaling X m

/- The positive-step scaling would follow from the root/log power law
(`EtaRootSystemLogPowerLaw`) together with the root power law for the
embedded shell units.  It is not the false invariant readout; the invariant
would force all logs to vanish, whereas scaling is the correct form.  No
scaling is assumed for positive `m`. -/
def EtaPartialReadoutScalingGap : Prop :=
  ¬ EtaPartialReadoutScalingPositive X

end LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScaling
