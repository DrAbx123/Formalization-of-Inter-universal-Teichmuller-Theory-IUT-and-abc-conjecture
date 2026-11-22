import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.GaussianSquareSum

/-!
# ShehddThetaGaussianChainActual — theta Gaussian kernel/value chain

New chain consequences of the compiled Gaussian theta kernel and square-sum facts: the
Gaussian exponent sign/bookkeeping, the theta value character laws, real positivity with
log formula, and the normalized Gaussian degree formula.  No new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddThetaGaussianChainActual

open LeanFormal.IUT
open scoped BigOperators

/-- **PROVED chain:** Gaussian exponent is nonnegative, even, and has the first-difference
formula. -/
theorem gaussExponent_chain (j : Int) :
    0 ≤ gaussExponent j ∧ gaussExponent (-j) = gaussExponent j ∧
      gaussExponent (j + 1) - gaussExponent j = 2 * j + 1 := by
  refine ⟨gaussExponent_nonneg j, ?_, gaussExponent_succ_sub j⟩
  simp

/-- **PROVED chain:** theta values form a symmetric character: unit at 0, invariance under
sign, and value/unit quotient equals q to the Gaussian exponent. -/
theorem thetaValue_chain {M : Type*} [CommGroup M] (q : M) (j : Int) :
    thetaValue q 0 = 1 ∧ thetaValue q (-j) = thetaValue q j ∧
      thetaValue q j / thetaValue q 0 = q ^ gaussExponent j := by
  refine ⟨thetaValue_zero q, ?_, thetaValue_div_zero q j⟩
  simp

/-- **PROVED chain:** real theta values are positive, their log is the Gaussian exponent
times log q, and they are symmetric. -/
theorem realThetaValue_chain {q : Real} (hq : 0 < q) (j : Int) :
    0 < realThetaValue q j ∧
      Real.log (realThetaValue q j) =
        (gaussExponent j).toNat * Real.log q ∧
        realThetaValue q (-j) = realThetaValue q j := by
  refine ⟨realThetaValue_pos hq j, ?_, ?_⟩
  · exact log_realThetaValue j
  · simp

/-- **PROVED chain:** the Gaussian square-sum formula and the normalized degree formula at
odd primes `l ≥ 5`. -/
theorem gaussianSquareSum_chain (l : Nat) (hodd : Odd l) (hl5 : 5 ≤ l) :
    gaussianSquareSum (lStar l) =
        (lStar l : Real) * ((lStar l : Real) + 1) * (2 * (lStar l : Real) + 1) / 6 ∧
      normalizedGaussianDegree l = (l : Real) * (l + 1) / 12 := by
  refine ⟨?_, normalizedGaussianDegree_eq_factor l hodd hl5⟩
  exact gaussianSquareSum_formula (lStar l)

end LeanFormal.IUT.XiFPaper.ShehddThetaGaussianChainActual
end
