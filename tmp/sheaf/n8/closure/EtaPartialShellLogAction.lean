import tmp.sheaf.n8.closure.EtaAdditiveLogInvariantAttempt
import tmp.sheaf.n8.closure.EtaAdditiveLogTransportActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPartialShellLogAction

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogInvariantAttempt
open LeanFormal.IUT.N8Closure.EtaAdditiveShellActionActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem fShellUnitToAlgClUnit_injective :
    Function.Injective (fShellUnitToAlgClUnit X) := by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  apply (fCompletionToPadicAlgCl X).injective
  have hcoe := congrArg (fun w : AlgClUnits X =>
    (w : PadicAlgCl (nativePrime X))) h
  simpa [fShellUnitToAlgClUnit] using hcoe

/-! ## Partial domain where the iterate remains in shell-unit image -/

def shellUnitImage : Set (AlgClUnits X) :=
  Set.range (fShellUnitToAlgClUnit X)

def goodShellUnit (m n : Nat) : Set ((fPlaceShell X).Units) :=
  {u | layerUnitAction X m n (fShellUnitToAlgClUnit X u) ∈ shellUnitImage X}

theorem goodShellUnit_zero (m : Nat) (u : (fPlaceShell X).Units) :
    u ∈ goodShellUnit X m 0 := by
  refine ⟨u, ?_⟩
  simp [layerUnitAction, layerIterate]

noncomputable def partialShellAction (m n : Nat)
    (u : (fPlaceShell X).Units) (h : u ∈ goodShellUnit X m n) :
    (fPlaceShell X).Units :=
  Classical.choose h

theorem partialShellAction_spec (m n : Nat)
    (u : (fPlaceShell X).Units) (h : u ∈ goodShellUnit X m n) :
    fShellUnitToAlgClUnit X (partialShellAction X m n u h) =
      layerUnitAction X m n (fShellUnitToAlgClUnit X u) := by
  exact Classical.choose_spec h

theorem partialShellAction_zero (m : Nat) (u : (fPlaceShell X).Units) :
    partialShellAction X m 0 u (goodShellUnit_zero X m u) = u := by
  apply fShellUnitToAlgClUnit_injective X
  rw [partialShellAction_spec]
  simp [layerUnitAction, layerIterate]

/-! ## Exact readout/action gaps -/

/-- Exact readout compatibility target: the partial action does not change
the additive log point on the good domain. -/
def EtaPartialShellActionReadout (m n : Nat) : Prop :=
  ∀ (u : (fPlaceShell X).Units) (h : u ∈ goodShellUnit X m n),
    fShellLogPoint X (partialShellAction X m n u h) = fShellLogPoint X u

/-- Exact points where the iterate leaves the shell-unit image; no action is
defined there. -/
def EtaPartialShellActionExitSet (m n : Nat) :
    Set ((fPlaceShell X).Units) :=
  {u | u ∉ goodShellUnit X m n}

theorem goodShellUnit_iff_not_exit (m n : Nat) (u : (fPlaceShell X).Units) :
    u ∈ goodShellUnit X m n ↔ u ∉ EtaPartialShellActionExitSet X m n := by
  simp [EtaPartialShellActionExitSet]

end LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
