import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion

/-! Mainline: chain laws among the Frey/Legendre J height criteria equivalences. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FreyCriteriaChainActual

open LeanFormal.IUT

theorem abc_iff_freyJDenominator_chain :
    ABCConjecture ↔ ABCFreyJDenominatorHeightCriterion :=
  abcConjecture_iff_freyJProductHeightCriterion.trans
    freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion

theorem freyJDenominator_vs_product :
    ABCFreyJDenominatorHeightCriterion ↔ ABCFreyJProductHeightCriterion :=
  freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion.symm

theorem abc_iff_legendreJProduct_chain :
    ABCConjecture ↔ ABCLegendreJProductHeightCriterion :=
  abcConjecture_iff_legendreJProductHeightCriterion

theorem legendreJDenominator_vs_product :
    ABCLegendreJDenominatorHeightCriterion ↔
      ABCLegendreJProductHeightCriterion :=
  freyJDenominatorHeightCriterion_iff_legendreJDenominatorHeightCriterion

end LeanFormal.IUT.XiFPaper.Mzk1FreyCriteriaChainActual