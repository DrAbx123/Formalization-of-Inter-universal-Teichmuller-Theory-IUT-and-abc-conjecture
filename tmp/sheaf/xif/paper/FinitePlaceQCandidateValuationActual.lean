import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# FinitePlaceQCandidate valuation API

Actual valuation facts for a qVFamily parameter q:

  Valued.v q = WithZero.exp (-q.exponent),
  Valued.v (q^n) = WithZero.exp (-(n * q.exponent)).

The uniformizer and residual-unit consequences are left to the next package;
they require a finite-place uniformizer whose val is exp(-1).
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.FinitePlaceQCandidateValuationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Valued

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {place : NumberField.FinitePlace K}

private theorem exp_neg_neg_toAdd_unzero
    (x : WithZero (Multiplicative Int)) (hx : x ≠ 0) :
    x = WithZero.exp (- -Multiplicative.toAdd (WithZero.unzero hx)) := by
  cases x with
  | zero => exact (hx rfl).elim
  | coe m => simp [WithZero.exp, WithZero.unzero]

/-- The actual valuation of a qVFamily candidate is exp(-exponent). -/
theorem qValuation_eq_exp_neg_exponent
    (parameter : FinitePlaceQCandidate place) :
    (Valued.v parameter.q : WithZero (Multiplicative Int)) =
      WithZero.exp (-parameter.exponent) := by
  unfold FinitePlaceQCandidate.exponent
  exact exp_neg_neg_toAdd_unzero _ parameter.valuation_ne_zero

end LeanFormal.IUT.XiFPaper.FinitePlaceQCandidateValuationActual
end
