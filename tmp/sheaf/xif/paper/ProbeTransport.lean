import tmp.sheaf.xif.paper.PaperC3SourceQHullRelationActual
namespace LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l) (b : Bad (nativePlaceSelection T))
example : Block (G := sourceQGeometry (l := l) T b) = SourceQTensorBlock T b := rfl
example : (paperQUnitLambda (G := sourceQGeometry (l := l) T b) : Block (G := sourceQGeometry (l := l) T b)) = (sourceQTensorUnit T b : SourceQTensorBlock T b) := rfl
end LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual