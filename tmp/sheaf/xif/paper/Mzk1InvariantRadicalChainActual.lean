import LeanFormal.IUT.ABCBridge.Arithmetic.ABCInvariantRadicalBridge
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence

/-! Mainline: combine the abc-invariant denominator/radical log bounds with the
  accepted dictionary `arithmeticWeight = log radical(product)` (new theorems). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1InvariantRadicalChainActual

open LeanFormal.IUT

theorem arithmeticWeight_bounds_abcJInvariant_den {a b c : Nat}
    (h : IsABCTriple a b c) :
    Real.log (radical (abcJInvariant a b c).den : Real) ≤
        arithmeticWeight (abcRationalPoint a c) ∧
      arithmeticWeight (abcRationalPoint a c) ≤
        Real.log (radical (abcJInvariant a b c).den : Real) + Real.log 2 := by
  rw [← radical_log_eq_arithmeticWeight h]
  exact h.abcJInvariant_den_logRadical_bounds

theorem height_le_log_abcJInvariant_den_radical {a b c : Nat}
    (h : IsABCTriple a b c) {A : Real}
    (hA : Height.logHeight₁ (abcRationalPoint a c) ≤
      arithmeticWeight (abcRationalPoint a c) + A) :
    Height.logHeight₁ (abcRationalPoint a c) ≤
      Real.log (radical (abcJInvariant a b c).den : Real) + Real.log 2 + A := by
  have hbounds := arithmeticWeight_bounds_abcJInvariant_den h
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1InvariantRadicalChainActual