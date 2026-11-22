import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierHeightWeightRefutation

/-!
# ShehddFrontierShortcutRefutedConsumerActualAdapted — refuted frontier shortcut consumer

STEP 0 prior-art (reuse only; A475 search: refutation assets found at tree):
* ABCFrontierHeightWeightRefutation.lean proves the F4a clause refutation via the
  explicit ABC triple (1,8,9): not_FrontierHeightWeightClause,
  not_ABCFrontierGapReduced, not_ABCFrontierGapReducedV2,
  not_ABCFrontierPointwiseWeakened;
* ABCFrontierSingletonReduction.lean: not_ABCFrontierPointwiseReduced.

This file packages the refuted shortcut routes as one consumer record: all reduced
frontier variants are empty, while the unreduced ABCFrontier (equivalent to ABC) is
unaffected.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFrontierShortcutRefutedConsumerActualAdapted

open LeanFormal.IUT

universe u

/-- **PROVED consumer:** the F4a height-weight clause fails, hence all reduced frontier
variants (gap-reduced gap v2, pointwise weakened, pointwise reduced) are uninhabited. -/
theorem frontier_shortcuts_refuted :
    ¬ FrontierHeightWeightClause ∧
      ¬ ABCFrontierGapReduced.{u} ∧
        ¬ ABCFrontierGapReducedV2.{u} ∧
          ¬ ABCFrontierPointwiseWeakened.{u} ∧
            ¬ ABCFrontierPointwiseReduced.{u} :=
  ⟨not_FrontierHeightWeightClause,
    not_ABCFrontierGapReduced,
    not_ABCFrontierGapReducedV2,
    not_ABCFrontierPointwiseWeakened,
    not_ABCFrontierPointwiseReduced⟩

/-- **PROVED consumer:** the F4a refutation at the explicit triple (1,8,9). -/
theorem frontier_f4a_counterexample :
    (1 + 1 / 10 : ℝ) * arithmeticWeight (abcRationalPoint 1 9) <
      Height.logHeight₁ (abcRationalPoint 1 9) :=
  oneAdd_tenth_mul_arithmeticWeight_lt_logHeight₁_one_eight_nine

/-- Row record: refuted routes vs retained (unreduced) frontier. -/
def frontierShortcutRows : List (String × String × String) :=
  [ ("F4a height-weight clause fails at (1,8,9)", "PROVED REFUTATION", "not_FrontierHeightWeightClause + oneAdd_tenth_..._one_eight_nine")
  , ("ABCFrontierGapReduced / V2 uninhabited", "PROVED REFUTATION", "not_ABCFrontierGapReduced / not_ABCFrontierGapReducedV2")
  , ("pointwise weakened/reduced uninhabited", "PROVED REFUTATION", "not_ABCFrontierPointwiseWeakened / not_ABCFrontierPointwiseReduced")
  , ("unreduced ABCFrontier", "UNAFFECTED (equivalent to ABC)", "ABCFrontier.abcFrontier_iff_abcConjecture")
  , ("F4a repair with slack constant", "EQUIVALENT TO ABC (no reduction)", "ABCHeightWeightAdditiveBoundV2 (abcConjecture_iff_ABCHeightWeightAdditiveBoundV2)") ]

theorem frontierShortcutRows_length : frontierShortcutRows.length = 5 := rfl

#check frontier_shortcuts_refuted
#check frontier_f4a_counterexample
#check frontierShortcutRows_length

end LeanFormal.IUT.XiFPaper.ShehddFrontierShortcutRefutedConsumerActualAdapted
end
