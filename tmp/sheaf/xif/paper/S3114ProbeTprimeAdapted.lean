import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
noncomputable section
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable (hT : T.arithmetic = S1280Arithmetic fiveLabel)
def Tprime : SourceNativeInitialThetaData.{0} fiveLabel := by
  cases hT
  exact T
example : Tprime T hT = T := rfl
#check Tprime T hT
