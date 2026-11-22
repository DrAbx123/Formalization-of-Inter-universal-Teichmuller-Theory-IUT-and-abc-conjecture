import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import tmp.sheaf.xif.paper.FinitePlaceQCandidateValuationActual

/-!
# Uniformizer valuation for a finite place

Explicit finite place place : FinitePlaceAtPrime K p and uniformizer pi of the
completed valuation at place.val.  Proves

  Valued.v pi = WithZero.exp (-1).
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.UniformizerValuationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Valued

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- The uniformizer as a field element of the completion. -/
noncomputable def qVUniformizerField
    (pi : (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).Uniformizer) : Completion place.val :=
  ((pi.1 : ((Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).valuationSubring)) :
    (underlyingPrime place.val).adicCompletion K)

/-- The actual valuation of the chosen uniformizer is exp(-1). -/
theorem qVUniformizerField_valuation
    (pi : (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).Uniformizer) :
    Valued.v (qVUniformizerField place pi) = WithZero.exp (-1) := by
  unfold qVUniformizerField
  exact uniformizer_valued_eq_exp_neg_one
    (K := K) (v := underlyingPrime place.val) pi


/-- The chosen uniformizer powers have valuation exp(-n). -/
theorem qVUniformizerField_pow_valuation
    (pi : (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).Uniformizer) (n : Nat) :
    Valued.v ((qVUniformizerField place pi) ^ n) =
      WithZero.exp (-(n : Int)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, map_mul, ih, qVUniformizerField_valuation, ← WithZero.exp_add]
      congr 1
      push_cast
      ring

/-- Actual qVFamily residual q / pi^order. -/
noncomputable def qVResidual
    (parameter : FinitePlaceQCandidate place.val)
    (pi : (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).Uniformizer) : Completion place.val :=
  parameter.q / (qVUniformizerField place pi) ^ parameter.order



/-- Exact missing residual valuation object (instance annotation needed for
Valued.v on Completion place.val). -/
structure QVResidualValuationGap where
  residual_valuation_one : Prop
  residual_integral : Prop
  residual_inverse_integral : Prop
  residual_unit : Prop
  residual_norm_one : Prop

end LeanFormal.IUT.XiFPaper.UniformizerValuationActual
end
