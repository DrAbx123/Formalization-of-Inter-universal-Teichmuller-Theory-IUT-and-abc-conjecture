import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline: bundle of all four accepted ABC forms (new conjunctions via proved equivalences). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1FormsBundleActual

open LeanFormal.IUT

/-- ABC gives simultaneously the log form, the height-weight form and the additive V2 form. -/
theorem all_forms_of_abc (h : ABCConjecture) :
    ABCLogConjecture ∧ (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∧
      ABCHeightWeightAdditiveBoundV2 :=
  ⟨abcConjecture_iff_abcLogConjecture.mp h,
   abcConjecture_iff_abcArithmeticWeightHeightBound.mp h,
   abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp h⟩

/-- Conversely, any one of the equivalent forms recovers ABC (plus the others). -/
theorem abc_of_any_form
    (h : ABCLogConjecture ∨ (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∨
      ABCHeightWeightAdditiveBoundV2) :
    ABCConjecture := by
  rcases h with h | h | h
  · exact abcConjecture_iff_abcLogConjecture.mpr h
  · exact abcConjecture_iff_abcArithmeticWeightHeightBound.mpr h
  · exact abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h

theorem abc_iff_any_form :
    ABCConjecture ↔
      (ABCLogConjecture ∨ (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∨
        ABCHeightWeightAdditiveBoundV2) :=
  ⟨fun h => Or.inl (all_forms_of_abc h).1, abc_of_any_form⟩

end LeanFormal.IUT.XiFPaper.Mzk1FormsBundleActual