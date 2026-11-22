import tmp.sheaf.xif.paper.PaperUnifiedLZetaCarrierActual
import Mathlib.RingTheory.TensorProduct.Finite
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual
namespace LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l) (b : Bad (nativePlaceSelection T))
example : FiniteDimensional ℚ_[qVFamTensorP T b] (UnifiedCarrier T b) := inferInstance
noncomputable def testBasis := Module.finBasis ℚ_[qVFamTensorP T b] (UnifiedCarrier T b)
end LeanFormal.IUT.XiFPaper.PaperUnifiedLZetaCarrierActual
