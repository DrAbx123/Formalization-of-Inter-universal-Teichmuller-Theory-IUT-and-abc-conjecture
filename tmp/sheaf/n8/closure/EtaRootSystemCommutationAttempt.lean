import tmp.sheaf.n8.closure.EtaPartialReadoutPositiveAttempt

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRootSystemCommutationAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaPartialReadoutActual
open LeanFormal.IUT.N8Closure.EtaPartialReadoutPositiveAttempt
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact root/log power law needed by the root-system commutation: on a
shell-unit preimage of the root iterate, the `(m+1)`-fold log equals the
original shell log.  This is the algebraic root/log law not supplied by
production `rootSystemPowRoot` (which supplies the power law on units,
not the logMap relation). -/
def EtaRootSystemLogPowerLaw (m : Nat) : Prop :=
  ∀ (u : (fPlaceShell X).Units)
    (_h : layerUnitAction X m 1 (fShellUnitToAlgClUnit X u) ∈ shellUnitImage X)
    (v : (fPlaceShell X).Units),
    fShellUnitToAlgClUnit X v =
      layerUnitAction X m 1 (fShellUnitToAlgClUnit X u) →
    ((m + 1 : Nat) • ((fPlaceShell X).logMap v).toAdd) =
      ((fPlaceShell X).logMap u).toAdd

/-- If the readout commutation and the root/log power law both hold at
`m > 0`, every good shell log is zero.  This is the decisive obstruction: a
nonzero shell log refutes the pair. -/
theorem commutation_and_powerLaw_force_log_zero
    (m : Nat) (hm : 0 < m)
    (hcomm : EtaLayerRootSystemReadoutCommutation X m 1)
    (hpow : EtaRootSystemLogPowerLaw X m)
    (u : (fPlaceShell X).Units)
    (hgood : layerUnitAction X m 1 (fShellUnitToAlgClUnit X u)
      ∈ shellUnitImage X) :
    ((fPlaceShell X).logMap u).toAdd = 0 := by
  let v : (fPlaceShell X).Units := Classical.choose hgood
  have hv : fShellUnitToAlgClUnit X v =
      layerUnitAction X m 1 (fShellUnitToAlgClUnit X u) :=
    Classical.choose_spec hgood
  have hlogv : fShellLogPoint X v = fShellLogPoint X u := hcomm u hgood v hv
  have hlogv' : ((fPlaceShell X).logMap v).toAdd =
      ((fPlaceShell X).logMap u).toAdd :=
    (fCompletionToPadicAlgCl X).injective hlogv
  have hpowv := hpow u hgood v hv
  have hlog_eq : ((m + 1 : Nat) • ((fPlaceShell X).logMap u).toAdd) =
      ((fPlaceShell X).logMap u).toAdd := by
    rw [hlogv'] at hpowv
    exact hpowv
  have hlog_cast : ((m + 1 : Nat) : (fPlaceShell X).K) *
      ((fPlaceShell X).logMap u).toAdd =
      ((fPlaceShell X).logMap u).toAdd := by
    simpa [nsmul_eq_mul] using hlog_eq
  have hmul : ((m : (fPlaceShell X).K) *
      ((fPlaceShell X).logMap u).toAdd) = 0 := by
    have hcast : ((m + 1 : Nat) : (fPlaceShell X).K) =
        (m : (fPlaceShell X).K) + 1 := by
      push_cast; ring
    rw [hcast, add_mul, one_mul] at hlog_cast
    have h := congrArg (fun x => x - ((fPlaceShell X).logMap u).toAdd) hlog_cast
    simpa [add_sub_cancel_right] using h
  have hm_ne : (m : (fPlaceShell X).K) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hm
  exact (mul_eq_zero.mp hmul).resolve_left hm_ne

/-- Decisive conditional no-go: a nonzero shell log at `m > 0` rules out the
pair (readout commutation, root/log power law). -/
theorem commutation_and_powerLaw_noGo_of_nonzero_log
    (m : Nat) (hm : 0 < m)
    (u : (fPlaceShell X).Units)
    (hgood : layerUnitAction X m 1 (fShellUnitToAlgClUnit X u)
      ∈ shellUnitImage X)
    (hlog : ((fPlaceShell X).logMap u).toAdd ≠ 0) :
    ¬ (EtaLayerRootSystemReadoutCommutation X m 1 ∧
      EtaRootSystemLogPowerLaw X m) := by
  rintro ⟨hcomm, hpow⟩
  exact hlog (commutation_and_powerLaw_force_log_zero X m hm hcomm hpow u hgood)

/-! ## Exact missing law -/

/- Production `rootSystemPowRoot` supplies the unit power law, but the
root/log power relation above is not available.  This is the missing
root-system/logMap algebraic law; no commutation or power law is assumed. -/

end LeanFormal.IUT.N8Closure.EtaRootSystemCommutationAttempt
