/- P6 display from sandwich 2. -/
import tmp.sheaf.xif.paper.Mzk1P6HCor312SupplyFromP5Actual
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P6DisplayFromSandwich2
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
theorem p6DisplayFromSandwich2 (D : P6DisplaySourceData)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid D.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap D.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs D.toTerms :=
  p6_display_chain D hCor312
#check p6DisplayFromSandwich2
end LeanFormal.IUT.XiFPaper.P6DisplayFromSandwich2
end
