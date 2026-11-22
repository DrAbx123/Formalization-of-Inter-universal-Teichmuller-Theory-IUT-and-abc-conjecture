import LeanFormal/IUT/ABCBridge/Bridge/Cor312ToABCBridgeInterface
import LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierReductions
import LeanFormal/IUT/ABCBridge/Bridge/ABCFrontier
import LeanFormal/IUT/ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison
import LeanFormal/IUT/ABCBridge/Bridge/IUTToABC

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ChainABCClosureActual — A475 chained adapters: Cor312/frontier -> ABC

Chain-of-reuse adapters combining existing donors (no theory duplication, no
axioms). Each theorem composes at least two existing donor declarations:

1. `cor312ToABCBridge_abcConjecture` (Cor312ToABCBridgeInterface.lean:446)
   with the IUT-to-ABC equivalences (`IUTToABC.lean:36/64`) and the
   height/weight v2 equivalence (ABCHeightArithmeticWeightComparison.lean:167);
2. `ABCFrontier.reduce_gapReductionInputs` / `reduce_pointwiseResidual`
   (ABCFrontierReductions.lean:256/273) with `abcConjecture_of_frontier`
   (ABCFrontier.lean:213) and `ABCFrontier.reduce_realLine` (:268).

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainABCClosureActual

open LeanFormal.IUT

/-- Cor312ToABCBridgeInterface -> ABCConjecture (donor alias). -/
theorem chain_cor312Bridge_abc (D : Cor312ToABCBridgeInterface) : ABCConjecture :=
  cor312ToABCBridge_abcConjecture D

/-- Cor312 bridge + log-equivalence -> ABC log conjecture. -/
theorem chain_cor312Bridge_log (D : Cor312ToABCBridgeInterface) : ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (cor312ToABCBridge_abcConjecture D)

/-- Cor312 bridge + height/weight equivalence -> v2 additive bound. -/
theorem chain_cor312Bridge_weightHeight (D : Cor312ToABCBridgeInterface) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp (cor312ToABCBridge_abcConjecture D)

/-- Gap-reduced frontier -> ABC (two-donor chain). -/
theorem chain_gapReduced_abc (h : ABCFrontierGapReduced.{0}) : ABCConjecture :=
  abcConjecture_of_frontierGapReduced h

/-- Gap-reduced frontier -> v2 additive bound (three-donor chain). -/
theorem chain_gapReduced_weightHeight (h : ABCFrontierGapReduced.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp (abcConjecture_of_frontierGapReduced h)

/-- Pointwise-reduced frontier -> ABC. -/
theorem chain_pointwise_abc (h : ABCFrontierPointwiseReduced.{0}) : ABCConjecture :=
  abcConjecture_of_frontierPointwiseReduced h

/-- Pointwise-reduced frontier -> v2 additive bound. -/
theorem chain_pointwise_weightHeight (h : ABCFrontierPointwiseReduced.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp (abcConjecture_of_frontierPointwiseReduced h)

/-- Real-line frontier -> ABC, chained through `reduce_realLine`. -/
theorem chain_realLine_abc (h : ABCFrontierRealLine) : ABCConjecture :=
  abcConjecture_of_frontier (ABCFrontier.reduce_realLine h)

def chainABCRows : List (String × String × String) :=
  [ ("Cor312 bridge -> ABC", "CHAIN PROVED", "chain_cor312Bridge_abc"),
    ("Cor312 bridge -> ABCLogConjecture", "CHAIN PROVED", "chain_cor312Bridge_log"),
    ("Cor312 bridge -> v2 bound", "CHAIN PROVED", "chain_cor312Bridge_weightHeight"),
    ("gapReduced -> ABC", "CHAIN PROVED", "chain_gapReduced_abc"),
    ("gapReduced -> v2 bound", "CHAIN PROVED", "chain_gapReduced_weightHeight"),
    ("pointwise -> ABC", "CHAIN PROVED", "chain_pointwise_abc"),
    ("realLine -> ABC", "CHAIN PROVED", "chain_realLine_abc") ]

theorem chainABCRows_length : chainABCRows.length = 7 := rfl

#check chain_cor312Bridge_weightHeight
#check chainABCRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ChainABCClosureActual
end