import tmp.sheaf.n8.closure.EtaAdditiveLogTransportActual

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaAdditiveLogInvariantAttempt

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaLogLinkCommonClosure
open LeanFormal.IUT.N8Closure.EtaCommonShellActionActual
open LeanFormal.IUT.N8Closure.EtaAdditiveLogTransportActual
open LeanFormal.IUT.N8Closure.EtaAdditiveShellActionActual
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open ABCBridge.N8.C3TensorTargetCorrection
open scoped Padic

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-! ## Actual partial log on the F-shell units -/

/-- Actual partial additive log: on the genuine F-shell units it is exactly
`fShellLogPoint` (which is `embedding(logMap u)`). -/
def partialShellLog : (fPlaceShell X).Units → PadicAlgCl (nativePrime X) :=
  fun u => fShellLogPoint X u

theorem partialShellLog_apply (u : (fPlaceShell X).Units) :
    partialShellLog X u = fShellLogPoint X u := rfl

theorem partialShellLog_eq_logMap (u : (fPlaceShell X).Units) :
    partialShellLog X u =
      fCompletionToPadicAlgCl X ((fPlaceShell X).logMap u).toAdd := rfl

/-! ## Total-log target (exact domain gap) -/

/- The target asks for a total p-adic log on the algebraic-closure unit group
(`AlgClUnits`) which restricts to `logMap` on the actual F-shell units and is
invariant under the root-system log-link iterate.  Production provides
`unitLog` only on `(Integers K)ˣ` for a complete nonarch local field `K`,
not on the algebraic closure unit group.  Thus the missing item is a total
p-adic log/domain extension; no arbitrary map is introduced. -/
structure EtaTotalAlgClLog (X : N8NativeInput l) where
  toAdd : AlgClUnits X → PadicAlgCl (nativePrime X)
  toAdd_shell : ∀ u : (fPlaceShell X).Units,
    toAdd (fShellUnitToAlgClUnit X u) = fShellLogPoint X u
  toAdd_logLink_invariant : ∀ (m n : Nat) (u : AlgClUnits X),
    toAdd (layerIterate X m n u) = toAdd u

def EtaTotalAlgClLogMissing : Prop :=
  ¬ Nonempty (EtaTotalAlgClLog X)

/-! ## Exact gap -/

/- No total p-adic logarithm on `AlgClUnits` is constructed in production.
The available logarithm is `unitLog` on the integral units of a complete
nonarch local field; the algebraic closure is not such a local field and the
unit group includes arbitrary nonzero algebraic elements.  The missing
declaration is therefore a total log/domain extension with the two stated
laws.  The target above is not inhabited and no action is asserted. -/
def EtaAdditiveLogInvariantGap : Prop :=
  EtaTotalAlgClLogMissing X

end LeanFormal.IUT.N8Closure.EtaAdditiveLogInvariantAttempt
