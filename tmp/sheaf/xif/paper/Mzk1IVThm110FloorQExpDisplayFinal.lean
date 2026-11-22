/- IV floor qExp display final. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110FloorQExpDisplayActual
import tmp.sheaf.xif.paper.Mzk1IVThm110HCor312FloorQExpActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayFinal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110HCor312FloorQExpActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
theorem floorQExpDisplay_final (A : ActualThm110Data)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid A.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap A.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs A.toTerms :=
  floorQExp_display A hCor312
#check floorQExpDisplay_final
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayFinal
end
