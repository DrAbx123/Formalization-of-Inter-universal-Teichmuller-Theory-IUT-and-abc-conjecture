/- IV N5 display chain final 2. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110N5DisplayChainFinal
import tmp.sheaf.xif.paper.Mzk1IVThm110N5Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5DisplayChainFinal2
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Actual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5DisplayChainFinal
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
theorem n5DisplayChainFinal2 {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    Nonempty (S3013QSource T) ∧
      qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  ⟨⟨actualS3013QSource T⟩, native_qSideSignedValueCondition_actual T⟩
#check n5DisplayChainFinal2
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5DisplayChainFinal2
end
