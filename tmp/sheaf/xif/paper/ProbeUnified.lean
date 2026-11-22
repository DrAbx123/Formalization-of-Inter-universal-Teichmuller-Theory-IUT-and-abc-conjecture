import tmp.sheaf.xif.paper.PaperUnifiedLZetaCarrierActual
import tmp.sheaf.xif.paper.PaperRootBaseLZetaActual
open LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual
namespace LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
example : FiniteDimensional ℚ_[qVFamTensorP T b] (UnifiedCarrier T b) := inferInstance
example : Module.FinBasis ℚ_[qVFamTensorP T b] (UnifiedCarrier T b) := inferInstance
end LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual
