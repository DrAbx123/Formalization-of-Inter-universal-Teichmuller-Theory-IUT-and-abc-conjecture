/- IV N5 + display chain. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110N5Final
import tmp.sheaf.xif.paper.Mzk1IVThm110DisplayFinal
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5DisplayChainActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5Final
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110DisplayFinal
open LeanFormal.IUT.XiFPaper.S3013QSideSignedValueCondition
theorem n5_and_display {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (A : ActualThm110Data)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid A.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap A.toTerms) :
    qSideSignedValueCondition (S3013QPilot T) (S3013QSigned T) ∧
      S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
        S3171IUTIVSection1DisplayActual.thm110Rhs A.toTerms :=
  ⟨n5_final T, display_final A hCor312⟩
#check n5_and_display
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110N5DisplayChainActual
end
