import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion

/-!
# ShehddInterfaceEllipticCriteriaChainActual — interface => elliptic height criteria chain

New chain: the Cor 3.12 -> ABC bridge interface implies each of the four compiled
elliptic-model height criteria (the tree only states criterion <-> ABC separately).  No new
assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInterfaceEllipticCriteriaChainActual

open LeanFormal.IUT

universe u

/-- **PROVED chain:** the interface implies the Frey j-product height criterion. -/
theorem freyJProductHeightCriterion_of_interface
    (D : Cor312ToABCBridgeInterface.{u}) :
    ABCFreyJProductHeightCriterion :=
  abcConjecture_iff_freyJProductHeightCriterion.mp
    (cor312ToABCBridge_abcConjecture D)

/-- **PROVED chain:** the interface implies the Legendre j-product height criterion. -/
theorem legendreJProductHeightCriterion_of_interface
    (D : Cor312ToABCBridgeInterface.{u}) :
    ABCLegendreJProductHeightCriterion :=
  abcConjecture_iff_legendreJProductHeightCriterion.mp
    (cor312ToABCBridge_abcConjecture D)

/-- **PROVED chain:** the interface implies the Frey j-denominator height criterion. -/
theorem freyJDenominatorHeightCriterion_of_interface
    (D : Cor312ToABCBridgeInterface.{u}) :
    ABCFreyJDenominatorHeightCriterion :=
  abcConjecture_iff_freyJDenominatorHeightCriterion.mp
    (cor312ToABCBridge_abcConjecture D)

/-- **PROVED chain:** the interface implies the Legendre j-denominator height criterion. -/
theorem legendreJDenominatorHeightCriterion_of_interface
    (D : Cor312ToABCBridgeInterface.{u}) :
    ABCLegendreJDenominatorHeightCriterion :=
  abcConjecture_iff_legendreJDenominatorHeightCriterion.mp
    (cor312ToABCBridge_abcConjecture D)

end LeanFormal.IUT.XiFPaper.ShehddInterfaceEllipticCriteriaChainActual
end
