/- Floor qExp + display chain. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312FloorQExpActual
import tmp.sheaf.xif.paper.Mzk1IVThm110DisplayFinal
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110DisplayFinal
theorem floorQExp_display (A : ActualThm110Data)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid A.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap A.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs A.toTerms :=
  display_final A hCor312
#check floorQExp_display
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayActual
end
