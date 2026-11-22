import LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierReductions
import LeanFormal/IUT/ABCBridge/Bridge/IUTToABC
import LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerABCFrontierFormsActual — A476 real consumer theorems (frontier forms)

New conclusions composing the ABC-frontier reduction slots
(`ABCFrontierReductions.lean:256/273/301/307`) with the ABC equivalence forms
(`IUTToABC.lean:36/64`, `ABCHeightArithmeticWeightComparison.lean:167`):
a gap-reduced/pointwise-reduced frontier yields the ABC log form and the
height/weight additive-bound form directly.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerABCFrontierFormsActual

open LeanFormal.IUT

/-- Gap-reduced frontier -> ABC log conjecture (frontier + log equivalence). -/
theorem gapReduced_logConjecture (h : ABCFrontierGapReduced.{0}) : ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (abcConjecture_of_frontierGapReduced h)

/-- Gap-reduced frontier -> height/weight v2 bound. -/
theorem gapReduced_weightHeight (h : ABCFrontierGapReduced.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp (abcConjecture_of_frontierGapReduced h)

/-- Pointwise-reduced frontier -> ABC log conjecture. -/
theorem pointwise_logConjecture (h : ABCFrontierPointwiseReduced.{0}) : ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (abcConjecture_of_frontierPointwiseReduced h)

/-- Pointwise-reduced frontier -> height/weight v2 bound. -/
theorem pointwise_weightHeight (h : ABCFrontierPointwiseReduced.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp (abcConjecture_of_frontierPointwiseReduced h)

/-- Gap-reduced frontier -> bridge interface whose log form holds. -/
theorem gapReduced_bridge_log (h : ABCFrontierGapReduced.{0}) :
    ABCLogConjecture :=
  gapReduced_logConjecture h

#check gapReduced_logConjecture

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerABCFrontierFormsActual
end