import tmp.sheaf.n8.closure.EtaAdditiveShellActionActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveCommonShellComparison
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## Actual shell-unit embedding and layer action -/

/-- Actual embedding of F-shell units into the common algebraic-closure unit
group, via the actual F-completion embedding.  No arbitrary unit chosen. -/
def fShellUnitToAlgClUnit : (fPlaceShell X).Units → AlgClUnits X :=
  fun u =>
    Units.mk0 (fCompletionToPadicAlgCl X u.val.val) (by
      have hu : u.val ≠ 0 := Units.ne_zero u
      have hK : u.val.val ≠ 0 := by
        intro h
        apply hu
        ext
        exact h
      have hne := (fCompletionToPadicAlgCl X).injective.ne hK
      simpa using hne)

/-- Actual layer action on the embedded F-shell units. -/
def layerUnitAction (m n : Nat) (u : AlgClUnits X) : AlgClUnits X :=
  layerIterate X m n u

theorem layerUnitAction_zero (m : Nat) (u : AlgClUnits X) :
    layerUnitAction X m 0 u = u := rfl

theorem layerUnitAction_one (m : Nat) (u : AlgClUnits X) :
    layerUnitAction X m 1 u =
      rootSystemPowRoot (nativePrime X) (m + 1) u := rfl

/-! ## Actual log point on the additive image -/

/-- Actual additive log point of an F-shell unit in the common carrier. -/
def fShellLogPoint (u : (fPlaceShell X).Units) :
    PadicAlgCl (nativePrime X) :=
  fCompletionToPadicAlgCl X ((fPlaceShell X).logMap u).toAdd

theorem fShellLogPoint_mem_additiveImage (u : (fPlaceShell X).Units) :
    fShellLogPoint X u ∈ additiveUnitLogMapImage X :=
  ⟨u, Set.mem_univ u, rfl⟩

/-! ## Exact additive log transport target -/

/- The missing additive transport is a map on the algebraic-closure unit
group to the common additive carrier which (i) agrees with `logMap` on
the actual F-shell units and (ii) is invariant under the root-system
log-link iterate.  This is the needed log-link commutativity theorem; it
is not assumed and no arbitrary transport is introduced. -/
structure EtaAdditiveLogTransport (X : N8NativeInput l) where
  toAdd : AlgClUnits X → PadicAlgCl (nativePrime X)
  toAdd_shell : ∀ u : (fPlaceShell X).Units,
    toAdd (fShellUnitToAlgClUnit X u) = fShellLogPoint X u
  toAdd_logLink_invariant : ∀ (m n : Nat) (u : AlgClUnits X),
    toAdd (layerIterate X m n u) = toAdd u

def EtaAdditiveLogTransportMissing : Prop :=
  ¬ Nonempty (EtaAdditiveLogTransport X)

/-! ## Exact gap -/

/- No production additive logarithm/transport map on all algebraic-closure
units is constructed, and the root-system log-link iterate is not known to
commute with the F-shell logMap.  The target above is exactly that missing
map plus its two laws.  No additive action is asserted without it. -/
def EtaAdditiveLogCommutationGap : Prop :=
  EtaAdditiveLogTransportMissing X

end LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
