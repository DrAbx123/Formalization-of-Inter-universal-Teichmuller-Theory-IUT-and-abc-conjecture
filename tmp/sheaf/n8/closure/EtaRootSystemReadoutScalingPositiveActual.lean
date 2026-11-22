import tmp.sheaf.n8.closure.EtaRootSystemReadoutScaling
import Mathlib.Algebra.Group.TypeTags.Basic

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScalingPositiveActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaPartialReadoutActual
open LeanFormal.IUT.N8Closure.EtaPartialReadoutPositiveAttempt
open LeanFormal.IUT.N8Closure.EtaRootSystemCommutationAttempt
open LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScaling
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem fShellUnitToAlgClUnit_pow
    (u : (fPlaceShell X).Units) (N : Nat) :
    fShellUnitToAlgClUnit X (u ^ N) =
      (fShellUnitToAlgClUnit X u) ^ N := by
  apply Units.ext
  change fCompletionToPadicAlgCl X ((u ^ N).val.val) =
    (fCompletionToPadicAlgCl X u.val.val) ^ N
  rw [show (u ^ N).val = u.val ^ N from Units.val_pow_eq_pow_val u N]
  rw [SubmonoidClass.coe_pow, map_pow]

/-- Actual power law: the shell-unit embedding preserves powers.  This is
the algebraic bridge that turns `rootSystemPowRoot_pow` into a power
statement for the F-shell unit preimage. -/
def EtaShellUnitEmbeddingPowLaw : Prop :=
  ∀ (u : (fPlaceShell X).Units) (N : Nat),
    fShellUnitToAlgClUnit X (u ^ N) =
      (fShellUnitToAlgClUnit X u) ^ N

/-- Conditional actual positive scaling: if the shell-unit embedding preserves
powers, then the corrected scaling `(m+1) • logMap(action) = logMap u`
holds on the whole good domain. -/
theorem partialReadoutScalingPositive_of_powLaw
    (hpowMap : EtaShellUnitEmbeddingPowLaw X) :
    EtaPartialReadoutScalingPositive X := by
  intro m hm u h
  let v : (fPlaceShell X).Units := partialShellAction X m 1 u h
  have hv : fShellUnitToAlgClUnit X v =
      layerUnitAction X m 1 (fShellUnitToAlgClUnit X u) :=
    partialShellAction_spec X m 1 u h
  have hpow : (fShellUnitToAlgClUnit X v) ^ (m + 1) =
      fShellUnitToAlgClUnit X u := by
    rw [hv, layerUnitAction_one, rootSystemPowRoot_pow]
    exact Nat.succ_ne_zero m
  have hpow' : v ^ (m + 1) = u :=
    fShellUnitToAlgClUnit_injective X (by
      rw [hpowMap]; exact hpow)
  have hlog : ((fPlaceShell X).logMap (v ^ (m + 1))).toAdd =
      ((fPlaceShell X).logMap u).toAdd := by rw [hpow']
  have hmul : ((m + 1 : Nat) •
      ((fPlaceShell X).logMap v).toAdd) =
      ((fPlaceShell X).logMap u).toAdd := by
    rw [← hlog, map_pow]
    simpa using Multiplicative.toAdd_pow ((fPlaceShell X).logMap v) (m + 1)
  simpa [v, partialShellAction] using hmul

theorem partialReadoutScalingPositive :
    EtaPartialReadoutScalingPositive X :=
  partialReadoutScalingPositive_of_powLaw X
    (fun u N => fShellUnitToAlgClUnit_pow X u N)

end LeanFormal.IUT.N8Closure.EtaRootSystemReadoutScalingPositiveActual
