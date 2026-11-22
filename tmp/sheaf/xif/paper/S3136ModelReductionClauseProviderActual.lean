import tmp.sheaf.xif.paper.NativeSplitSufficientConditionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-! # Stage-4 host: model reduction-clause provider from a split-input family

Source anchors: IUT I, Definition 3.1 (reduction clause of the initial Theta data); IUT III,
Definition 3.1 (bad multiplicative reduction); IUT I, Example 3.2, (iv) (concrete Gaussian
arithmetic).

CONSUMER: qpilot's modelSourceDefinition31Data assembly. The reduction slot of
SourceDefinition31Data (stable + multiplicative + split-multiplicative + q-parameter clauses
over the selected/bad place partition) is provided conditionally on the actual split-input
family of the native initial Theta datum (one split-reduction input at every native bad
lift). This reuses the proved nativeReductionClause_of_splitInputFamily from the native
closure stream; no general split theorem is asserted, and no arbitrary certificate is chosen.

LABEL: prerequisite component. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelReductionClauseProviderActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Conditional provider of the model reduction clause from a native split-input family. -/
noncomputable def lgpModelReductionClauseProvider
    (F : NativeSplitInputFamily (l := l) T) :
    Theorem311Source.SourceReductionClause
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) :=
  nativeReductionClause_of_splitInputFamily T F

/-- The provided reduction clause has the native selected/bad place partition. -/
theorem lgpModelReductionClauseProvider_partition
    (F : NativeSplitInputFamily (l := l) T) :
    (lgpModelReductionClauseProvider (l := l) T F).partition =
      toSourcePlacePartition (nativePlaceSelection T) := rfl

#check lgpModelReductionClauseProvider
#check lgpModelReductionClauseProvider_partition

end LeanFormal.IUT.XiFPaper.S3136ModelReductionClauseProviderActual
end