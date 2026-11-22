import LeanFormal.IUT.Foundations.Theta.OddTheta

/-!
# ShehddOddThetaSignChainActual — odd theta sign/exponent chain

New chain consequences of the compiled odd theta sign and exponent laws: the sign is a
norm-one multiplicative character with inverse law, the exponent is the natural part of
n(n+1)/2, and the zero term is U.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddOddThetaSignChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- **PROVED chain:** the odd theta sign is multiplicative, norm one, and its inverse is
the negative-index sign. -/
theorem oddThetaSign_chain (m n : Int) :
    oddThetaSign (L := L) (m + n) =
        oddThetaSign (L := L) m * oddThetaSign (L := L) n ∧
      ‖oddThetaSign (L := L) n‖ = 1 ∧
        oddThetaSign (L := L) n * oddThetaSign (L := L) (-n) = 1 := by
  refine ⟨oddThetaSign_add m n, norm_oddThetaSign n, ?_⟩
  rw [← oddThetaSign_add, add_neg_cancel, oddThetaSign_zero]

/-- **PROVED chain:** the theta exponent is the integer formula n(n+1)/2 and the zero
term is U. -/
theorem oddThetaExponent_term_chain (q U : L) (n : Int) :
    (oddThetaExponent n : Int) = n * (n + 1) / 2 ∧
      oddThetaTerm q U 0 = U := by
  refine ⟨oddThetaExponent_coe n, ?_⟩
  exact oddThetaTerm_zero q U

/-- **PROVED chain:** the sign at -1 is -1 and at 0 is 1. -/
theorem oddThetaSign_special_values :
    oddThetaSign (L := L) 0 = 1 ∧ oddThetaSign (L := L) (-1) = -1 :=
  ⟨oddThetaSign_zero, oddThetaSign_neg_one⟩

end LeanFormal.IUT.XiFPaper.ShehddOddThetaSignChainActual
end
