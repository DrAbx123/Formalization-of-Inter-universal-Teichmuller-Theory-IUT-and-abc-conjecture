import tmp.sheaf.xif.paper.Mzk1G1ProtectedToZeroMapActual
import tmp.sheaf.xif.paper.Mzk1Consumer24AdapterUnconditionalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalPsiComponentActual
open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterUnconditionalActual

variable {K : Type*} [Field K] [DecidableEq K]

/-- G-C protected-to-zero component: all protected points map to `0`, and the
`0`-fiber has simple (unramified) points. -/
theorem protectedToZero_component (T : Finset K) :
    (∀ t ∈ T, Polynomial.eval t (protectedToZeroPolynomial T) = 0) ∧
    (∀ t ∈ T, Polynomial.eval t
      (Polynomial.derivative (protectedToZeroPolynomial T)) ≠ 0) :=
  ⟨fun t ht => eval_protectedToZero_of_mem ht,
    fun t ht => eval_derivative_protectedToZero_ne_zero ht⟩

/-- G-C finite-beta component: the existing finite-beta corrected base. -/
theorem finiteBeta_component : FiniteBetaCorrectedBase :=
  finiteBetaCorrectedBase_proved

#print axioms protectedToZero_component
#print axioms finiteBeta_component
end LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalPsiComponentActual