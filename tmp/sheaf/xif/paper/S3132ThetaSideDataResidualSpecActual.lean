import tmp.sheaf.xif.paper.S3136ConcreteExample36NativeDataActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1200000

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3136ConcreteExample36NativeDataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideDataResidualSpecActual

/-! # Paper-route Theta side: exact data residual record for the native tuple

The precise remaining data for the concrete Example 3.6 SourceNativeInitialThetaData:
a SourceInitialThetaTuple over the concrete Gaussian arithmetic together with the
six clauses A--F of IUT I, Definition 3.1 (data fields, not opaque Props).
stage4's record LGPConcreteExample36NativeDataMissing l is adopted as THE data
residual; lgpConcreteExample36NativeData is the constructive passage to the native
datum. Component, not a paper object; owner hull. -/

variable {l : PrimeGeFive}

/-- Exact data residual (nonempty form of stage4's data record). -/
def ThetaSideNativeDataResidual : Prop :=
  Nonempty (LGPConcreteExample36NativeDataMissing l)

/-- The data residual is exactly stage4's record. -/
theorem thetaSideNativeDataResidual_iff :
    ThetaSideNativeDataResidual (l := l) ↔
      Nonempty (LGPConcreteExample36NativeDataMissing l) :=
  Iff.rfl

/-- From the exact data residual one obtains the concrete native initial-Theta
datum (constructive passage, stage4). -/
def thetaSideNativeData_of_residual
    (h : ThetaSideNativeDataResidual (l := l)) :
    SourceNativeInitialThetaData.{0} l :=
  lgpConcreteExample36NativeData (Classical.choice h)

/-- The constructed datum has the concrete Gaussian arithmetic. -/
theorem thetaSideNativeData_of_residual_arithmetic
    (h : ThetaSideNativeDataResidual (l := l)) :
    (thetaSideNativeData_of_residual (l := l) h).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  lgpConcreteExample36NativeData_arithmetic _

#check ThetaSideNativeDataResidual
#check thetaSideNativeDataResidual_iff
#check thetaSideNativeData_of_residual
#check thetaSideNativeData_of_residual_arithmetic

end LeanFormal.IUT.XiFPaper.S3132ThetaSideDataResidualSpecActual
end
