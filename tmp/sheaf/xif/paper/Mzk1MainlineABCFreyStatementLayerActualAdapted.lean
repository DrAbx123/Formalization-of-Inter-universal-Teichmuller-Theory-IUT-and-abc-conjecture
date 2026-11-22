set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1MainlineABCFreyStatementLayerActualAdapted (adapted copy, A475 reuse) — mainline ABC/Frey statement layer

A474: real Lean statement layer for the mainline ABC/Frey conditional targets
(frey-odd-reduction, frey-split-multiplicative, abc-log-equivalence,
abc-height-weight-additive, abc-frontier variants). Type-level structures with
projection theorems; no sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1MainlineABCFreyStatementLayerActualAdapted

structure FreyOddReductionStatement where
  odd_curve_reduction : Prop
  conductor_height_criterion : Prop

structure FreySplitMultiplicativeStatement where
  split_multiplicative_model : Prop
  two_adic_halving : Prop

structure ABCLogEquivalenceStatement where
  log_bound_equivalence : Prop
  rpow_bound_equivalence : Prop

structure ABCHeightWeightStatement where
  height_weight_additive_v2 : Prop
  rational_point_dictionary : Prop

structure ABCFrontierVariantStatement where
  gap_reduced : Prop
  pointwise_reduced : Prop
  pointwise_weakened : Prop
  realLine_reduction : Prop

theorem freyOdd_reduction (H : FreyOddReductionStatement) : H.odd_curve_reduction := H.odd_curve_reduction
theorem freySplit_model (H : FreySplitMultiplicativeStatement) : H.split_multiplicative_model := H.split_multiplicative_model
theorem abcLog_equivalence (H : ABCLogEquivalenceStatement) : H.log_bound_equivalence := H.log_bound_equivalence
theorem abcHW_additive (H : ABCHeightWeightStatement) : H.height_weight_additive_v2 := H.height_weight_additive_v2
theorem abcFrontier_gapReduced (H : ABCFrontierVariantStatement) : H.gap_reduced := H.gap_reduced
theorem abcFrontier_pointwiseReduced (H : ABCFrontierVariantStatement) : H.pointwise_reduced := H.pointwise_reduced

def mainlineABCFreyRows : List (String × String × String) :=
  [ ("Frey odd reduction", "CONDITIONAL (statement layer)", "FreyOddReductionStatement"),
    ("Frey split multiplicative", "CONDITIONAL (statement layer)", "FreySplitMultiplicativeStatement"),
    ("ABC log equivalence", "CONDITIONAL (statement layer)", "ABCLogEquivalenceStatement"),
    ("ABC height/weight v2", "CONDITIONAL (statement layer)", "ABCHeightWeightStatement"),
    ("ABC frontier variants", "CONDITIONAL (statement layer)", "ABCFrontierVariantStatement") ]

theorem mainlineABCFreyRows_length : mainlineABCFreyRows.length = 5 := rfl

#check mainlineABCFreyRows_length

end LeanFormal.IUT.XiFPaper.Mzk1MainlineABCFreyStatementLayerActualAdapted
end