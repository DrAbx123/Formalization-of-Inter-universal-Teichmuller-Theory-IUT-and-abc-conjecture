/- G1P8 P6 display chain. -/
import tmp.sheaf.xif.paper.Mzk1G1P8P6DisplayV2Actual
import tmp.sheaf.xif.paper.Mzk1G1P8P6DisplayActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayChainActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayActual
theorem p6_display_chain_final (D : P6DisplaySourceData)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid D.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap D.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs D.toTerms :=
  g1p8P6_display_final D hCor312
#check p6_display_chain_final
end LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayChainActual
end
