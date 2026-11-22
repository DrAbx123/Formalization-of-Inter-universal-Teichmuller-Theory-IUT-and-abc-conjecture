import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: new equivalences/cross-form consumers between the logarithmic form and
  the additive V2 form (composed from proved equivalences with ABC). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogFormChainActual

open LeanFormal.IUT

theorem heightWeight_of_logConjecture (h : ABCLogConjecture) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mp
    (abcConjecture_iff_abcLogConjecture.mpr h)

theorem v2_of_logConjecture (h : ABCLogConjecture) :
    ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp
    (abcConjecture_iff_abcLogConjecture.mpr h)

theorem logConjecture_iff_v2 :
    ABCLogConjecture ↔ ABCHeightWeightAdditiveBoundV2 :=
  abcConjecture_iff_abcLogConjecture.symm.trans
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2

end LeanFormal.IUT.XiFPaper.Mzk1LogFormChainActual