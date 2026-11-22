import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-! Mainline (T5/T6): package from the additive V2 contract: all accepted ABC forms
  together with the per-epsilon bound family (new composed conjunction). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1V2PackageActual

open LeanFormal.IUT

theorem v2Package (h : ABCHeightWeightAdditiveBoundV2) :
    ABCConjecture ∧ ABCLogConjecture ∧ (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∧
      (∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
        ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) := by
  have habc : ABCConjecture :=
    abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr h
  exact ⟨habc,
    abcConjecture_iff_abcLogConjecture.mp habc,
    abcConjecture_iff_abcArithmeticWeightHeightBound.mp habc,
    fun epsilon hepsilon => h epsilon hepsilon⟩

end LeanFormal.IUT.XiFPaper.Mzk1V2PackageActual