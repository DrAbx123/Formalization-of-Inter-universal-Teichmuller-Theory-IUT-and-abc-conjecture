/- G1P8 P6 display chain v2. -/
import tmp.sheaf.xif.paper.P6DisplayChainActual
import tmp.sheaf.xif.paper.Mzk1G1P8P6DisplayV2Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayChainV2
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.P6DisplayChainActual
open LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
theorem p6ChainV2_display (D : P6DisplaySourceData)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid D.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap D.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs D.toTerms :=
  p6Chain_display D hCor312
#check p6ChainV2_display
end LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayChainV2
end
