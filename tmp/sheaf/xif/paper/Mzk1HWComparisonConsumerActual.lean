import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-! # iutiv-abc:HW.add consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HWComparisonConsumerActual

open LeanFormal.IUT

theorem hwConsumer_iff : ABCConjecture ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

theorem hwConsumer_exists (h : ABCHeightWeightAdditiveBoundV2)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  ABCHeightWeightAdditiveBoundV2.exists_constant h hepsilon

def hwConsumerRows : List (String × String × String) :=
  [ ("ABC iff v2 bound", "PROVED", "hwConsumer_iff (IUTToABC equivalence)"),
    ("v2 consumer API at epsilon", "PROVED", "hwConsumer_exists"),
    ("uniform valuation bound route", "REFUTED/vacuous", "kept as documentation in tree") ]

theorem hwConsumerRows_length : hwConsumerRows.length = 3 := rfl

#check hwConsumer_iff
#check hwConsumerRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HWComparisonConsumerActual
end