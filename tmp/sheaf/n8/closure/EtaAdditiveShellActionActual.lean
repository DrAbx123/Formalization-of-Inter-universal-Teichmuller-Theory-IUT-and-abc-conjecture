import tmp.sheaf.n8.closure.EtaAdditiveUnitLogComparisonActual
import tmp.sheaf.n8.closure.EtaCommonShellActionActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaAdditiveShellActionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveUnitLogComparisonActual
open LeanFormal.IUT.N8Closure.EtaAdditiveCommonShellComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## Actual layer action laws -/

/-- Actual root-system log-link iterate on the algebraic-closure units. -/
def layerIterate (m : Nat) : (n : Nat) → AlgClUnits X → AlgClUnits X
  | 0 => id
  | n + 1 => fun u =>
      rootSystemPowRoot (nativePrime X) (m + n + 1)
        (layerIterate m n u)

theorem layerIterate_zero (m : Nat) (u : AlgClUnits X) :
    layerIterate X m 0 u = u := rfl

theorem layerIterate_one (m : Nat) (u : AlgClUnits X) :
    layerIterate X m 1 u =
      rootSystemPowRoot (nativePrime X) (m + 1) u := rfl

/-! ## Actual additive image inclusion -/

theorem additiveImage_subset_commonShell :
    additiveUnitLogMapImage X ⊆ additiveCommonShell X :=
  additiveUnitLogComparison_actual X

/-! ## Exact transport no-go -/

/-- The naive unit transport would send an F-shell unit `u` to a layer unit
whose coercion is the additive value `logMap(u).toAdd`.  It is impossible
already at `u = 1`: the right side is zero, while a unit is nonzero. -/
def EtaNaiveAdditiveUnitTransport : Prop :=
  ∃ toLayer : (fPlaceShell X).Units → AlgClUnits X,
    ∀ u, ((toLayer u : AlgClUnits X) : PadicAlgCl (nativePrime X)) =
      fCompletionToPadicAlgCl X (((fPlaceShell X).logMap u).toAdd)

theorem etaNaiveAdditiveUnitTransport_noGo :
    ¬ EtaNaiveAdditiveUnitTransport X := by
  rintro ⟨toLayer, h⟩
  have h1 := h 1
  have h1' : ((toLayer 1 : AlgClUnits X) : PadicAlgCl (nativePrime X)) =
      fCompletionToPadicAlgCl X (((fPlaceShell X).logMap
        (1 : (fPlaceShell X).Units)).toAdd) := h1
  rw [show ((fPlaceShell X).logMap (1 : (fPlaceShell X).Units)).toAdd = 0 by simp] at h1'
  have hmap0 : fCompletionToPadicAlgCl X (0 : (fPlaceShell X).K) = 0 := map_zero _
  rw [hmap0] at h1'
  exact (Units.ne_zero (toLayer 1)) h1'

/-! ## Exact additive action gap -/

/- An additive log-link action on `additiveUnitLogMapImage` would need an
actual additive transport from the root-system layer to the F-shell additive
carrier, not a coercion of log values to units (which is impossible by the
no-go above).  No such production transport is constructed; the action is
therefore not asserted and no field multiplication is used. -/
def EtaAdditiveTransportGap : Prop :=
  ¬ Nonempty (EtaNaiveAdditiveUnitTransport X)

end LeanFormal.IUT.N8Closure.EtaAdditiveShellActionActual
