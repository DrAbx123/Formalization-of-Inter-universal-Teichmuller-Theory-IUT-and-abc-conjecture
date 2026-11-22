/- P6 display sandwich final. -/
import tmp.sheaf.xif.paper.P6DisplayFromSandwich2
import tmp.sheaf.xif.paper.Mzk1P6HCor312ActualFromP5Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P6DisplaySandwichFinal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.P6DisplayFromSandwich2
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
theorem p6DisplaySandwichFinal (D : P6DisplaySourceData)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid D.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap D.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs D.toTerms :=
  p6DisplayFromSandwich2 D hCor312
#check p6DisplaySandwichFinal
end LeanFormal.IUT.XiFPaper.P6DisplaySandwichFinal
end
