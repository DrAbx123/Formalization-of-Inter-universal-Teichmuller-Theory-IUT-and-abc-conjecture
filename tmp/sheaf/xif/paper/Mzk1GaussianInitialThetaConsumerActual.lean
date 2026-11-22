import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

/-!
# Mzk1GaussianInitialThetaConsumerActual — consumer theorems over the concrete Gaussian
initial-theta arithmetic example (tree asset, OLEAN_FRESH). Composed projections only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GaussianInitialThetaConsumerActual

open LeanFormal.IUT

/-- Consumer: the Gaussian polynomial X^2+1 is irreducible over Q. -/
theorem consumer_gaussianPolynomial_irreducible : Irreducible gaussianPolynomial :=
  gaussianPolynomial_irreducible

/-- Consumer: the Gaussian field has a square root of -1. -/
theorem consumer_gaussianField_sqrtNegOne : HasSqrtNegOne GaussianField :=
  gaussianField_sqrtNegOne

/-- Consumer: the Gaussian identity theta tower exists for every l >= 5. -/
theorem consumer_gaussianIdentityThetaTower (l : PrimeGeFive) :
    ThetaFieldTower l GaussianField GaussianField GaussianField :=
  gaussianIdentityThetaTower l

/-- Consumer: the Gaussian punctured elliptic curve carrier. -/
def consumer_gaussianPuncturedCurve : PuncturedEllipticCurve GaussianField :=
  gaussianPuncturedCurve

#check consumer_gaussianPolynomial_irreducible
#check consumer_gaussianField_sqrtNegOne
#check consumer_gaussianIdentityThetaTower
#check consumer_gaussianPuncturedCurve

end LeanFormal.IUT.XiFPaper.Mzk1GaussianInitialThetaConsumerActual
end
