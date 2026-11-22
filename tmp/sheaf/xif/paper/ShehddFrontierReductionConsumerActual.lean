import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierReductions
import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierHeightWeightRefutation

/-!
# ShehddFrontierReductionConsumerActual — frontier reduction implications vs empty premises

STEP 0 prior-art (reuse only):
* ABCFrontierReductions.lean: FrontierHeightWeightClause and the other F1-F6 clauses,
  ABCFrontierGapReduced / ABCFrontierPointwiseReduced,
  reduce_gapReductionInputs / reduce_pointwiseResidual (into ABCFrontier);
* ABCFrontierHeightWeightRefutation.lean: F4a fails at (1,8,9) => all reduced frontier
  variants have empty premises.

This file records the consumer-level consequence: the reduction implications remain valid
but their premises are uninhabited; only the unreduced ABCFrontier (equivalent to ABC) is
unaffected.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFrontierReductionConsumerActual

open LeanFormal.IUT

universe u

/-- **PROVED consumer:** the two reduction implications into ABCFrontier hold, while
their reduced premises are refuted (F4a failure), so they are vacuous routes. -/
theorem frontier_reductions_with_empty_premises :
    (ABCFrontierGapReduced.{u} → ABCFrontier.{u}) ∧
      (ABCFrontierPointwiseReduced.{u} → ABCFrontier.{u}) ∧
        ¬ ABCFrontierGapReduced.{u} ∧
          ¬ ABCFrontierPointwiseReduced.{u} :=
  ⟨ABCFrontier.reduce_gapReductionInputs,
    ABCFrontier.reduce_pointwiseResidual,
    not_ABCFrontierGapReduced,
    not_ABCFrontierPointwiseReduced⟩

/-- **PROVED consumer:** the reduction implications and the refutation on the same page:
no reduced frontier route reduces the problem. -/
theorem frontier_reduction_routes_vacuous :
    (ABCFrontierGapReduced.{u} → ABCConjecture) ∧
      (ABCFrontierPointwiseReduced.{u} → ABCConjecture) :=
  ⟨fun h => abcConjecture_of_frontier (ABCFrontier.reduce_gapReductionInputs h),
    fun h => abcConjecture_of_frontier (ABCFrontier.reduce_pointwiseResidual h)⟩

/-- Row record: reduction implications vs refuted premises. -/
def frontierReductionRows : List (String × String × String) :=
  [ ("gapReduced => ABCFrontier", "PROVED (reduction retained)", "ABCFrontier.reduce_gapReductionInputs")
  , ("pointwiseReduced => ABCFrontier", "PROVED (reduction retained)", "ABCFrontier.reduce_pointwiseResidual")
  , ("F4a failure => both premises empty", "PROVED REFUTATION", "ABCFrontierHeightWeightRefutation.not_ABCFrontierGapReduced / not_ABCFrontierPointwiseReduced")
  , ("consequence: reduced routes do not reduce the problem", "PROVED CONSUMER", "frontier_reductions_with_empty_premises")
  , ("unreduced ABCFrontier", "UNAFFECTED (iff ABC)", "ABCFrontier.abcFrontier_iff_abcConjecture") ]

theorem frontierReductionRows_length : frontierReductionRows.length = 5 := rfl

#check frontier_reductions_with_empty_premises
#check frontier_reduction_routes_vacuous
#check frontierReductionRows_length

end LeanFormal.IUT.XiFPaper.ShehddFrontierReductionConsumerActual
end
