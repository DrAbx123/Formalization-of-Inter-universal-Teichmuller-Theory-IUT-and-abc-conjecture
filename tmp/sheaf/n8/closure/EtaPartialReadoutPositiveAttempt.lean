import tmp.sheaf.n8.closure.EtaPartialReadoutActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPartialReadoutPositiveAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaPartialReadoutActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact root-system/logMap commutation needed for the positive-step readout:
any shell-unit preimage of the layer iterate has the same F-shell log point. -/
def EtaLayerRootSystemReadoutCommutation (m n : Nat) : Prop :=
  ∀ (u : (fPlaceShell X).Units)
    (_h : layerUnitAction X m n (fShellUnitToAlgClUnit X u) ∈ shellUnitImage X)
    (v : (fPlaceShell X).Units),
    fShellUnitToAlgClUnit X v =
      layerUnitAction X m n (fShellUnitToAlgClUnit X u) →
    fShellLogPoint X v = fShellLogPoint X u

theorem partialReadout_iff_rootSystemCommutation (m n : Nat) :
    EtaPartialShellActionReadout X m n ↔
      EtaLayerRootSystemReadoutCommutation X m n := by
  constructor
  · intro h u hg v hv
    have hspec := partialShellAction_spec X m n u hg
    have hvu : v = partialShellAction X m n u hg :=
      fShellUnitToAlgClUnit_injective X (by
        rw [hv, hspec])
    subst hvu
    exact h u hg
  · intro h u hg
    have hspec := partialShellAction_spec X m n u hg
    exact h u hg (partialShellAction X m n u hg) hspec

theorem partialReadoutPositive_iff_rootSystemCommutation :
    EtaPartialReadoutPositive X ↔
      ∀ (m n : Nat), n ≠ 0 → EtaLayerRootSystemReadoutCommutation X m n := by
  constructor
  · intro h m n hn
    exact (partialReadout_iff_rootSystemCommutation X m n).mp (h m n hn)
  · intro h m n hn
    exact (partialReadout_iff_rootSystemCommutation X m n).mpr (h m n hn)

/-! ## Exact missing commutation law -/

/- The positive-step readout is exactly the root-system/logMap commutation
law above.  Production gives `rootSystemPowRoot` as a root-system iterate
and `fShellLogPoint = embedding ∘ logMap`, but no theorem commutes them on
shell-unit preimages.  This is the missing law; no readout is assumed. -/
def EtaRootSystemReadoutCommutationGap : Prop :=
  ¬ (∀ (m n : Nat), n ≠ 0 → EtaLayerRootSystemReadoutCommutation X m n)

end LeanFormal.IUT.N8Closure.EtaPartialReadoutPositiveAttempt
