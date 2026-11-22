import tmp.sheaf.xif.paper.GenericResidualValuationActual
import tmp.sheaf.xif.paper.UniformizerValuationActual

/-!
# Coherent explicit valuation on Completion place.val

We define the adic valuation explicitly from underlyingPrime place.val and
compare it with the Valued.v instance on Completion place.val.  If the equality
is definitional, the generic residual valuation lemma applies without any
cross-instance rewrite.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CompletionPlaceCoherentValuationActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped Valued

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- The explicit adic valuation on the Completion place. -/
noncomputable def completionPlaceValuation :
    Valuation (Completion place.val) (WithZero (Multiplicative Int)) :=
  (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
    (WithZero (Multiplicative Int)))

/-- Coherence with the canonical Valued.v instance. -/
theorem completionPlaceValuation_eq_valued :
    completionPlaceValuation place =
      (Valued.v : Valuation (Completion place.val)
        (WithZero (Multiplicative Int))) := rfl


/-- The coherent explicit valuation packaged with its actual equality to Valued.v. -/
noncomputable def coherentCompletionPlaceValuation :
    GenericResidualValuationActual.CoherentCompletionPlaceValuation
      (Completion place.val) where
  v := completionPlaceValuation place
  valued_v_eq :=
    completionPlaceValuation place =
      (Valued.v : Valuation (Completion place.val)
        (WithZero (Multiplicative Int)))
  valuation_instances_coherent :=
    completionPlaceValuation place =
      (Valued.v : Valuation (Completion place.val)
        (WithZero (Multiplicative Int)))

/-- Explicit residual valuation for qVFamily q / pi^order. -/
theorem qVResidual_valuation_explicit
    (parameter : FinitePlaceQCandidate place.val)
    (pi : (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).Uniformizer) :
    completionPlaceValuation place
      (UniformizerValuationActual.qVResidual place parameter pi) = 1 := by
  have hq : completionPlaceValuation place parameter.q =
      WithZero.exp (-parameter.exponent) := by
    simpa [completionPlaceValuation] using
      FinitePlaceQCandidateValuationActual.qValuation_eq_exp_neg_exponent parameter
  have hpi : completionPlaceValuation place
      (UniformizerValuationActual.qVUniformizerField place pi) =
      WithZero.exp (-1) := by
    simpa [completionPlaceValuation] using
      UniformizerValuationActual.qVUniformizerField_valuation place pi
  have hn : (parameter.order : Int) = parameter.exponent := by
    unfold FinitePlaceQCandidate.order
    exact Int.toNat_of_nonneg (le_of_lt parameter.exponent_pos)
  exact GenericResidualValuationActual.residual_valuation
    (completionPlaceValuation place) parameter.q
    (UniformizerValuationActual.qVUniformizerField place pi)
    parameter.order parameter.exponent hq hpi hn

/-- The same residual valuation stated with the canonical Valued.v. -/
theorem qVResidual_valued_valuation
    (parameter : FinitePlaceQCandidate place.val)
    (pi : (Valued.v : Valuation ((underlyingPrime place.val).adicCompletion K)
      (WithZero (Multiplicative Int))).Uniformizer) :
    Valued.v (UniformizerValuationActual.qVResidual place parameter pi) = 1 := by
  rw [← completionPlaceValuation_eq_valued]
  exact qVResidual_valuation_explicit place parameter pi

end LeanFormal.IUT.XiFPaper.CompletionPlaceCoherentValuationActual
end
