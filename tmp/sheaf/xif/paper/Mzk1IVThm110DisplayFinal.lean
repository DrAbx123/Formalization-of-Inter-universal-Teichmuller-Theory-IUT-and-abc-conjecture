/- IV Thm 1.10 display final. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110DisplayFinal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
theorem display_final (A : ActualThm110Data)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid A.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap A.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs A.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs A.toTerms :=
  thm110_display_of_hCor312 A hCor312
#check display_final
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110DisplayFinal
end
