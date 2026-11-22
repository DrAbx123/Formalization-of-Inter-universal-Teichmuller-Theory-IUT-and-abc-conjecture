/- G1/P8 P6 display v2. -/
import tmp.sheaf.xif.paper.Mzk1G1P8P6DisplayActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayV2Actual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayActual
theorem g1p8P6_display_final (D : P6DisplaySourceData)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid D.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap D.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs D.toTerms :=
  p6Actual_display D hCor312
#check g1p8P6_display_final
end LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayV2Actual
end
