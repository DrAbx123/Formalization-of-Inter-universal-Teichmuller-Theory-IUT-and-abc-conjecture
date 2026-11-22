import LeanFormal.IUT.Foundations.Theta.OddThetaTermAlgebra
import LeanFormal.IUT.Foundations.Theta.OddThetaShiftSum

/-!
# ShehddOddThetaAlgebraChainActual — odd theta exponent/sign/coefficient algebra chain

New chain consequences of the compiledtheta term algebra and tsum reindexing laws: the
doubled exponent identities, the sign algebra at norm level, the root conversion, the
norm of the shift coefficient, and the reindexed tsum laws.  No new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddOddThetaAlgebraChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Foundations.Theta

universe u

variable {L : Type u} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]

/-- **PROVED chain:** the doubled theta exponent is `n(n+1)`, with the cocycle identity
under shifts. -/
theorem oddThetaExponent_double_chain (n a : Int) :
    2 * (oddThetaExponent n : Int) = n * (n + 1) ∧
      2 * (oddThetaExponent (n + a) : Int) =
        2 * (oddThetaExponent n : Int) + a * (2 * n + a + 1) := by
  refine ⟨two_mul_oddThetaExponent_coe n, ?_⟩
  exact two_mul_oddThetaExponent_add n a

/-- **PROVED chain:** the sign squares to one and splits under a shift. -/
theorem oddThetaSign_algebra_chain (n a : Int) :
    oddThetaSign (L := L) n * oddThetaSign (L := L) n = 1 ∧
      oddThetaSign (L := L) n =
        oddThetaSign (L := L) (n + a) * oddThetaSign (L := L) a := by
  refine ⟨oddThetaSign_sq n, ?_⟩
  exact oddThetaSign_eq_shift n a

/-- **PROVED chain:** for `r^2 = q`, natural q-powers are even root powers; and the shift
coefficient has the expected norm. -/
theorem oddTheta_root_coefficient_chain (q r U : L) (hr : r ^ 2 = q) (k : Nat)
    (a : Int) :
    q ^ k = r ^ (2 * (k : Int)) ∧
      ‖oddThetaShiftCoefficient r U a‖ =
        ‖r‖ ^ (-(a ^ 2)) * ‖U‖ ^ (-(2 * a)) := by
  refine ⟨q_pow_eq_root_zpow q r hr k, ?_⟩
  unfold oddThetaShiftCoefficient
  rw [norm_mul, norm_mul, norm_oddThetaSign, one_mul]
  simp only [norm_zpow]

/-- **PROVED chain:** integer-indexed tsum reindexing laws and translated theta
summability. -/
theorem oddTheta_tsum_reindex_chain (q U : L) (hU : U ≠ 0) (hq : ‖q‖ < 1)
    (f : Int → L) (c : L) (a : Int) :
    (∑' n : Int, f (n + a)) = ∑' n : Int, f n ∧
      (∑' n : Int, c * f (n + a)) = c * ∑' n : Int, f n ∧
        Summable (fun n : Int => oddThetaTerm q U (n + a)) := by
  refine ⟨tsum_addRight_eq_tsum f a, tsum_const_mul_addRight_eq f c a, ?_⟩
  exact summable_oddThetaTerm_addRight q U hU hq a

end LeanFormal.IUT.XiFPaper.ShehddOddThetaAlgebraChainActual
end
