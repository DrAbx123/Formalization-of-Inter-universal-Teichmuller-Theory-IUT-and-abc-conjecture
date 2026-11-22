/- IV Thm 1.10 N5 final. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110N5Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Final
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Actual
theorem n5_final {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) :=
  native_qSideSignedValueCondition_actual T
theorem n5_source_final {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    Nonempty (S3013QSource T) :=
  ⟨actualS3013QSource T⟩
#check n5_final
#check n5_source_final
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Final
end
