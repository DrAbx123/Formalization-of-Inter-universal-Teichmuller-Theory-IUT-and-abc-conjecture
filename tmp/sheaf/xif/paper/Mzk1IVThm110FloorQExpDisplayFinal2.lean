/- IV floor qExp display final 2. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110FloorQExpDisplayFinal
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayFinal2
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayFinal
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
theorem floorQExpDisplayFinal2 (A : ActualThm110Data)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid A.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap A.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs A.toTerms :=
  floorQExpDisplay_final A hCor312
#check floorQExpDisplayFinal2
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110FloorQExpDisplayFinal2
end
