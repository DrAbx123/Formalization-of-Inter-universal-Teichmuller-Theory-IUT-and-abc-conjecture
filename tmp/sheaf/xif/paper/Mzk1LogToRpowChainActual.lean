import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-! Mainline (T6): from the logarithmic ABC form derive the radical-power family and
  combine it with the height-weight form (new consumers). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LogToRpowChainActual

open LeanFormal.IUT

theorem rpowFamily_of_logConjecture (h : ABCLogConjecture) :
    ∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧
      ∀ a b c : Nat, IsABCTriple a b c →
        (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon) := by
  intro epsilon hepsilon
  exact (abcLogBound_exists_iff_rpow_exists epsilon hepsilon).mp (h epsilon hepsilon)

theorem heightWeight_and_rpow_of_log (h : ABCLogConjecture) :
    (∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∧
      (∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon)) :=
  ⟨abcConjecture_iff_abcArithmeticWeightHeightBound.mp
     (abcConjecture_iff_abcLogConjecture.mpr h),
   rpowFamily_of_logConjecture h⟩

end LeanFormal.IUT.XiFPaper.Mzk1LogToRpowChainActual