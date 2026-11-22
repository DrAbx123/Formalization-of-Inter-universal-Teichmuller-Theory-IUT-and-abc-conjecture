import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-!
# ShehddABCFrontierFormEquivalencesActual — frontier => ABC log/additive forms

STEP 0 prior-art (reuse, no new math):
* ABCBridge/Bridge/ABCFrontier.lean: abcFrontier_iff_abcConjecture, abcConjecture_of_frontier;
* ABCBridge/Bridge/IUTToABC.lean: abcConjecture_iff_abcLogConjecture;
* ABCBridge/Arithmetic/ABCHeightArithmeticWeightComparison.lean:
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.

Composes the three PROVED equivalences/implications into the frontier-form and
log/additive-form statements.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddABCFrontierFormEquivalencesActual

open LeanFormal.IUT

/-- **PROVED composition:** the ABC frontier implies ABC in log form. -/
theorem abcLogConjecture_of_frontier (h : ABCFrontier.{0}) : ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (abcConjecture_of_frontier h)

/-- **PROVED composition:** the ABC frontier implies the additive height-weight form. -/
theorem abcHeightWeightAdditive_of_frontier (h : ABCFrontier.{0}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp (abcConjecture_of_frontier h)

/-- **PROVED composition:** ABCFrontier is equivalent to the log form. -/
theorem abcFrontier_iff_abcLogConjecture :
    ABCFrontier.{0} ↔ ABCLogConjecture :=
  abcFrontier_iff_abcConjecture.trans abcConjecture_iff_abcLogConjecture

/-- **PROVED composition:** ABCFrontier is equivalent to the additive form. -/
theorem abcFrontier_iff_abcHeightWeightAdditive :
    ABCFrontier.{0} ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcFrontier_iff_abcConjecture.trans abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

/-- Row record: reused equivalences vs composed statements. -/
def abcFrontierFormRows : List (String × String × String) :=
  [ ("ABCFrontier <-> ABCConjecture", "REUSED PROVED", "ABCFrontier.lean:abcFrontier_iff_abcConjecture")
  , ("ABCConjecture <-> ABCLogConjecture", "REUSED PROVED", "IUTToABC.lean:abcConjecture_iff_abcLogConjecture")
  , ("ABCConjecture <-> ABCHeightWeightAdditiveBoundV2", "REUSED PROVED", "ABCHeightArithmeticWeightComparison.lean:abcConjecture_iff_ABCHeightWeightAdditiveBoundV2")
  , ("frontier => log form", "COMPOSED PROVED", "abcLogConjecture_of_frontier")
  , ("frontier => additive form", "COMPOSED PROVED", "abcHeightWeightAdditive_of_frontier")
  , ("frontier <-> log form / additive form", "COMPOSED PROVED", "abcFrontier_iff_abcLogConjecture, abcFrontier_iff_abcHeightWeightAdditive") ]

theorem abcFrontierFormRows_length : abcFrontierFormRows.length = 6 := rfl

#check abcLogConjecture_of_frontier
#check abcHeightWeightAdditive_of_frontier
#check abcFrontier_iff_abcLogConjecture
#check abcFrontier_iff_abcHeightWeightAdditive
#check abcFrontierFormRows_length

end LeanFormal.IUT.XiFPaper.ShehddABCFrontierFormEquivalencesActual
end
