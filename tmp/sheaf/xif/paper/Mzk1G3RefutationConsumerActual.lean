import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontierHeightWeightRefutation
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1G3RefutationConsumerActual — G3 frontier routes REFUTED (consumer record)

DAG nodes: iutiv-abc:G3.route.gapReduced / gapReducedV2 / pointwiseWeakened /
pointwiseReduced.  ABCFrontierHeightWeightRefutation proves the frontier clauses are
false at (1,8,9): the gap-reduced, V2-refined and repaired pointwise frontiers are
all empty, and the original pointwise-reduced premise is also refuted.  Therefore the
corresponding route implications are valid but unusable; they are recorded BLOCKED.
No closure claim; gate NOT PASSED.  Registry frozen 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1G3RefutationConsumerActual

open LeanFormal.IUT

universe u

/-- The gap-reduced frontier is empty (refuted). -/
theorem gapReduced_refuted : ¬ ABCFrontierGapReduced.{u} :=
  not_ABCFrontierGapReduced

/-- The V2-refined gap frontier is empty (refuted). -/
theorem gapReducedV2_refuted : ¬ ABCFrontierGapReducedV2.{u} :=
  not_ABCFrontierGapReducedV2

/-- The repaired pointwise-weakened frontier is empty (refuted). -/
theorem pointwiseWeakened_refuted : ¬ ABCFrontierPointwiseWeakened.{u} :=
  not_ABCFrontierPointwiseWeakened

/-- The original pointwise-reduced frontier is empty (refuted). -/
theorem pointwiseReduced_refuted : ¬ ABCFrontierPointwiseReduced.{u} :=
  not_ABCFrontierPointwiseReduced

/-- Rows: refutation record. -/
def g3RefutationRows : List (String × String × String) :=
  [ ("gapReduced", "not_ABCFrontierGapReduced", "REFUTED"),
    ("gapReducedV2", "not_ABCFrontierGapReducedV2", "REFUTED"),
    ("pointwiseWeakened", "not_ABCFrontierPointwiseWeakened", "REFUTED"),
    ("pointwiseReduced", "not_ABCFrontierPointwiseReduced", "REFUTED"),
    ("scope", "frontier routes unusable; no ABC shortcut; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem g3RefutationRows_length : g3RefutationRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G3RefutationConsumerActual

end
