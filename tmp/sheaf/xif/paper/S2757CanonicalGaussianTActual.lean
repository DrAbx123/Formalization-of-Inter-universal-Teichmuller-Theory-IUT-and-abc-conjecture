import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2757CanonicalGaussianTActual

/-- Conditional canonical Gaussian T: from a supplied `SourceCompletion` whose
arithmetic is the Gaussian arithmetic, produce the native initial Theta data
with the required arithmetic. -/
noncomputable def S2757CanonicalGaussianT
    (C : SourceCompletion.{0} fiveLabel)
    (h : C.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) :
    SourceNativeInitialThetaData.{0} fiveLabel :=
  C.toSourceNativeInitialThetaData

theorem S2757_arithmetic_eq
    (C : SourceCompletion.{0} fiveLabel)
    (h : C.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) :
    (S2757CanonicalGaussianT C h).arithmetic =
      gaussianInitialThetaArithmeticData fiveLabel := by
  rw [S2757CanonicalGaussianT, C.toSourceNative_arithmetic, h]

theorem S2757_K_eq_GaussianField
    (C : SourceCompletion.{0} fiveLabel)
    (h : C.arithmetic = gaussianInitialThetaArithmeticData fiveLabel) :
    (S2757CanonicalGaussianT C h).arithmetic.K = GaussianField := by
  rw [S2757_arithmetic_eq C h]
  rfl

#check S2757CanonicalGaussianT
#check S2757_arithmetic_eq
#check S2757_K_eq_GaussianField

end LeanFormal.IUT.XiFPaper.S2757CanonicalGaussianTActual
end