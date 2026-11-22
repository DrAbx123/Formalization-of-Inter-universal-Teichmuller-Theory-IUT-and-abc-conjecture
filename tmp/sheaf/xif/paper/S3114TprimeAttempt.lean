import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3114TprimeAttempt

variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable (hT : T.arithmetic = S1280Arithmetic fiveLabel)

/-- Transport of the tuple field to S1280 arithmetic. -/
noncomputable def S3114Tuple :
    SourceInitialThetaTuple (S1280Arithmetic fiveLabel) :=
  hT ▸ T.tuple

/-- Exact source compatibility needed for clauseA: the transported tuple's
source must be the transported source. -/
def S3114TupleSourceTarget : Prop :=
  (S3114Tuple T hT).source = hT ▸ T.tuple.source

/-- Exact T' target. -/
def S3114TprimeTarget : Prop :=
  Nonempty (SourceNativeInitialThetaData.{0} fiveLabel)

#check S3114Tuple
#check S3114TupleSourceTarget
#check S3114TprimeTarget

end LeanFormal.IUT.XiFPaper.S3114TprimeAttempt
end