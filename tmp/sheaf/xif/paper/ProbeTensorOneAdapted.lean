import tmp.sheaf.xif.paper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
namespace LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l) (b : Bad (nativePlaceSelection T))
example : (1 : SourceQTensorBlock T b) = sourceQTensorLanding T b 1 := rfl
example : (1 : SourceQTensorBlock T b) = sourceQTensorLanding T b 1 := by simp [sourceQTensorLanding]
end LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual