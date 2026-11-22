import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-!
# ShehddFrontierFormsChainActual — ABCFrontier equivalence with the retained ABC forms

Chain theorems: the compiled `abcFrontier_iff_abcConjecture` is composed with the proved
ABC form equivalences, yielding direct frontier <-> log-form and frontier <-> additive-form
statements (new consequences; the tree states the pieces separately).  No new assumptions,
no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFrontierFormsChainActual

open LeanFormal.IUT

universe u

/-- **PROVED chain:** a frontier witness yields ABC in logarithmic form. -/
theorem abcLogConjecture_of_frontier (h : ABCFrontier.{u}) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (abcConjecture_of_frontier h)

/-- **PROVED chain:** a frontier witness yields the additive height-weight form. -/
theorem abcHeightWeightAdditive_of_frontier (h : ABCFrontier.{u}) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (abcConjecture_of_frontier h)

/-- **PROVED chain:** the unparameterized frontier is equivalent to the logarithmic form. -/
theorem abcFrontier_iff_abcLogConjecture :
    ABCFrontier.{0} ↔ ABCLogConjecture :=
  abcFrontier_iff_abcConjecture.trans abcConjecture_iff_abcLogConjecture

/-- **PROVED chain:** the unparameterized frontier is equivalent to the additive form. -/
theorem abcFrontier_iff_additive :
    ABCFrontier.{0} ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcFrontier_iff_abcConjecture.trans abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

end LeanFormal.IUT.XiFPaper.ShehddFrontierFormsChainActual
end
