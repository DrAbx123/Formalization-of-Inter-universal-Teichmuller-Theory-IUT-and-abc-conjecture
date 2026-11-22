import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
noncomputable section
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable (hT : T.arithmetic = S1280Arithmetic fiveLabel)
def hEq : T.arithmetic.Fmod = T.arithmetic.F :=
  (congrArg (fun A : InitialThetaArithmeticData fiveLabel => A.Fmod) hT).trans
    ((by rfl : (S1280Arithmetic fiveLabel).Fmod = (S1280Arithmetic fiveLabel).F).trans
      (congrArg (fun A : InitialThetaArithmeticData fiveLabel => A.F) hT).symm)
def eEq : NumberField.FinitePlace (T.arithmetic.Fmod) = NumberField.FinitePlace (T.arithmetic.F) := by
  cases hEq T hT
  rfl
#check eEq T hT
