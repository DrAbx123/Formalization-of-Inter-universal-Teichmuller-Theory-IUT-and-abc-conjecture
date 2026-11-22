import LeanFormal.IUT.ABCBridge.Bridge.ABCEllipticHeightCriterion

/-!
# ShehddEllipticHeightCriteriaConsumerActualAdapted — ABC elliptic height criteria consumer

STEP 0 prior-art (reuse only; A475 search: elliptic height criteria assets found):
* ABCBridge/Bridge/ABCEllipticHeightCriterion.lean:
  ABCFreyJProductHeightCriterion, ABCLegendreJProductHeightCriterion,
  ABCFreyJDenominatorHeightCriterion, ABCLegendreJDenominatorHeightCriterion and the
  proved equivalences abcConjecture_iff_{frey,legendre}J{Product,Denominator}HeightCriterion,
  freyJProductHeightCriterion_iff_legendreJProductHeightCriterion,
  freyJDenominatorHeightCriterion_iff_legendreJDenominatorHeightCriterion,
  freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion.

This file packages the four elliptic-model height criteria as one consumer: ABC is
equivalent to each of them, and the Frey product/denominator criteria are mutually
equivalent.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddEllipticHeightCriteriaConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** ABC is equivalent to all four elliptic height criteria, and the
Frey product/denominator criteria are equivalent to each other. -/
theorem elliptic_height_criteria_equivalent :
    (ABCConjecture ↔ ABCFreyJProductHeightCriterion) ∧
      (ABCConjecture ↔ ABCLegendreJProductHeightCriterion) ∧
        (ABCConjecture ↔ ABCFreyJDenominatorHeightCriterion) ∧
          (ABCConjecture ↔ ABCLegendreJDenominatorHeightCriterion) ∧
            (ABCFreyJProductHeightCriterion ↔ ABCFreyJDenominatorHeightCriterion) :=
  ⟨abcConjecture_iff_freyJProductHeightCriterion,
    abcConjecture_iff_legendreJProductHeightCriterion,
    abcConjecture_iff_freyJDenominatorHeightCriterion,
    abcConjecture_iff_legendreJDenominatorHeightCriterion,
    freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion⟩

/-- **PROVED consumer:** Frey product criterion <=> Legendre denominator criterion
(derived composition of the two proved equivalences). -/
theorem freyProduct_iff_legendreDenominator :
    ABCFreyJProductHeightCriterion ↔ ABCLegendreJDenominatorHeightCriterion :=
  abcConjecture_iff_freyJProductHeightCriterion.symm.trans
    abcConjecture_iff_legendreJDenominatorHeightCriterion

/-- Row record: reused criteria equivalences vs consumer bundle. -/
def ellipticHeightCriteriaRows : List (String × String × String) :=
  [ ("Frey product criterion <=> ABC", "REUSED PROVED", "abcConjecture_iff_freyJProductHeightCriterion")
  , ("Legendre product criterion <=> ABC", "REUSED PROVED", "abcConjecture_iff_legendreJProductHeightCriterion")
  , ("Frey / Legendre denominator criteria <=> ABC", "REUSED PROVED", "abcConjecture_iff_freyJDenominatorHeightCriterion / _legendreJDenominator...")
  , ("Frey product <=> Frey denominator", "REUSED PROVED", "freyJProductHeightCriterion_iff_freyJDenominatorHeightCriterion")
  , ("all-four consumer bundle + cross composition", "COMPOSED PROVED", "elliptic_height_criteria_equivalent, freyProduct_iff_legendreDenominator") ]

theorem ellipticHeightCriteriaRows_length : ellipticHeightCriteriaRows.length = 5 := rfl

#check elliptic_height_criteria_equivalent
#check freyProduct_iff_legendreDenominator
#check ellipticHeightCriteriaRows_length

end LeanFormal.IUT.XiFPaper.ShehddEllipticHeightCriteriaConsumerActualAdapted
end
