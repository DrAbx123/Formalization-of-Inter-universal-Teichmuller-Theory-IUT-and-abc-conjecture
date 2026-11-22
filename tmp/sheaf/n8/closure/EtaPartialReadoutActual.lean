import tmp.sheaf.n8.closure.EtaPartialShellLogAction

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaPartialReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaPartialShellLogAction
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual zero-step readout: at `n = 0` the partial action is the identity,
so the additive log point is unchanged on the whole good domain. -/
theorem etaPartialShellActionReadout_zero (m : Nat) :
    EtaPartialShellActionReadout X m 0 := by
  intro u h
  have hh : h = goodShellUnit_zero X m u := Subsingleton.elim h _
  subst hh
  rw [partialShellAction_zero]

/-! ## Exact positive-step gap -/

/-- Exact positive-step readout target: for every nonzero iterate length the
additive log point is unchanged on the good domain. -/
def EtaPartialReadoutPositive : Prop :=
  ∀ (m n : Nat), n ≠ 0 → EtaPartialShellActionReadout X m n

/- The positive-step readout would follow from a log-link commutation
theorem identifying `fShellLogPoint` of the partial action image with
`fShellLogPoint` of the original unit.  No such commutation between the
root-system iterate and the F-shell logMap is present in production; the
target is recorded, not assumed, and no readout is fabricated. -/
def EtaPartialReadoutLogLinkCommutation (m n : Nat) : Prop :=
  EtaPartialShellActionReadout X m n

def EtaPartialReadoutPositiveGap : Prop :=
  ¬ EtaPartialReadoutPositive X

end LeanFormal.IUT.N8Closure.EtaPartialReadoutActual
