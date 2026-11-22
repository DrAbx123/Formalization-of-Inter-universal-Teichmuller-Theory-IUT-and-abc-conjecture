import tmp.sheaf.xif.paper.S237SourceHullProperActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

/-!
# S241: noncompactness of the source tensor block

The source tensor block is a finite one-factor Q_p tensor, hence a normed
Q_p-vector space.  A nontrivial normed vector space over an infinite normed
field is noncompact.  Therefore the compact corrected qUnit hull is proper.
No inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S241SourceHullNoncompactActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.S237SourceHullProperActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual source tensor block is a nontrivial normed Q_p-vector space. -/
theorem sourceQTensorBlock_noncompactSpace :
    NoncompactSpace (SourceQTensorBlock T b) := by
  haveI : Infinite ℚ_[qVFamTensorP T b] := inferInstance
  haveI : Nontrivial (SourceQTensorBlock T b) := inferInstance
  exact NormedSpace.noncompactSpace ℚ_[qVFamTensorP T b]
    (SourceQTensorBlock T b)

/-- The corrected qUnit hull is not the whole source tensor carrier. -/
theorem sourceQTensorLambdaOHull_ne_univ_unconditional :
    sourceQTensorLambdaOHull T b ≠ Set.univ :=
  sourceQTensorLambdaOHull_ne_univ_of_noncompact T b
    (sourceQTensorBlock_noncompactSpace T b)

end LeanFormal.IUT.XiFPaper.S241SourceHullNoncompactActual

end
