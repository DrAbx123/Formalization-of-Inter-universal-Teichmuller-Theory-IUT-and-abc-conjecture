import LeanFormal.IUT.Foundations.Theta.GaussianKernel

/-!
# Mzk1GaussianPowerLawActual — derived multiplicativity/power laws for the Gaussian theta
kernel (new theorems from the existing GaussianKernel asset; no copies). No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GaussianPowerLawActual

open LeanFormal.IUT

/-- Derived: theta value at q*q is the square of theta value at q. -/
theorem realThetaValue_mul (q : ℝ) (j : ℤ) :
    realThetaValue (q * q) j = realThetaValue q j * realThetaValue q j := by
  unfold realThetaValue
  rw [mul_pow]

/-- Derived: theta value at q^k is the k-th power of theta value at q. -/
theorem realThetaValue_pow (q : ℝ) (j : ℤ) (k : ℕ) :
    realThetaValue (q ^ k) j = (realThetaValue q j) ^ k := by
  unfold realThetaValue
  rw [← pow_mul, mul_comm, pow_mul]

/-- Derived: theta value at a product is the product of theta values. -/
theorem realThetaValue_mulArg (q r : ℝ) (j : ℤ) :
    realThetaValue (q * r) j = realThetaValue q j * realThetaValue r j := by
  unfold realThetaValue
  rw [mul_pow]

/-- Derived: theta values are even and multiplicative at q*q. -/
theorem realThetaValue_neg_mul (q : ℝ) (j : ℤ) :
    realThetaValue (q * q) (-j) = realThetaValue q j * realThetaValue q j := by
  rw [realThetaValue_neg', realThetaValue_mul]

#check realThetaValue_mul
#check realThetaValue_pow
#check realThetaValue_mulArg
#check realThetaValue_neg_mul

end LeanFormal.IUT.XiFPaper.Mzk1GaussianPowerLawActual
end
