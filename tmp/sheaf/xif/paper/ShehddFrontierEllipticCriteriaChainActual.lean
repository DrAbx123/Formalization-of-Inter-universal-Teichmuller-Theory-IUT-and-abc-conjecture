import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion

/-!
# ShehddFrontierEllipticCriteriaChainActual — frontier => elliptic height criteria chain

Chain theorems: `abcConjecture_of_frontier` composed with the four compiled ABC <->
elliptic height criterion equivalences.  New consequences; no new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFrontierEllipticCriteriaChainActual

open LeanFormal.IUT

universe u

/-- **PROVED chain:** a frontier witness implies the Frey j-product height criterion. -/
theorem freyJProductHeightCriterion_of_frontier (h : ABCFrontier.{u}) :
    ABCFreyJProductHeightCriterion :=
  abcConjecture_iff_freyJProductHeightCriterion.mp (abcConjecture_of_frontier h)

/-- **PROVED chain:** a frontier witness implies the Legendre j-product height criterion. -/
theorem legendreJProductHeightCriterion_of_frontier (h : ABCFrontier.{u}) :
    ABCLegendreJProductHeightCriterion :=
  abcConjecture_iff_legendreJProductHeightCriterion.mp (abcConjecture_of_frontier h)

/-- **PROVED chain:** a frontier witness implies the Frey j-denominator height criterion. -/
theorem freyJDenominatorHeightCriterion_of_frontier (h : ABCFrontier.{u}) :
    ABCFreyJDenominatorHeightCriterion :=
  abcConjecture_iff_freyJDenominatorHeightCriterion.mp (abcConjecture_of_frontier h)

/-- **PROVED chain:** a frontier witness implies the Legendre j-denominator height
criterion. -/
theorem legendreJDenominatorHeightCriterion_of_frontier (h : ABCFrontier.{u}) :
    ABCLegendreJDenominatorHeightCriterion :=
  abcConjecture_iff_legendreJDenominatorHeightCriterion.mp (abcConjecture_of_frontier h)

/-- **PROVED chain:** the unparameterized frontier is equivalent to the Frey j-product
height criterion. -/
theorem abcFrontier_iff_freyJProductHeightCriterion :
    ABCFrontier.{0} ↔ ABCFreyJProductHeightCriterion :=
  abcFrontier_iff_abcConjecture.trans abcConjecture_iff_freyJProductHeightCriterion

end LeanFormal.IUT.XiFPaper.ShehddFrontierEllipticCriteriaChainActual
end
