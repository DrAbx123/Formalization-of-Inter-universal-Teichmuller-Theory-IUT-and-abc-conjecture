/- P6 display terms final. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplayTermsFinalActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
noncomputable def p6ActualDataV2 (D : P6DisplaySourceData) : ActualThm110Data := D.toActualData
noncomputable def p6ActualTermsV2 (D : P6DisplaySourceData) : Thm110DisplayTerms := D.toTerms
theorem p6Actual_displayV2 (D : P6DisplaySourceData)
    (hCor312 : thm110Lhs D.toTerms ≤ thm110Mid D.toTerms + thm110Cor312Gap D.toTerms) :
    thm110Lhs D.toTerms ≤ thm110Rhs D.toTerms := p6_display_chain D hCor312
#check p6ActualDataV2
#check p6ActualTermsV2
#check p6Actual_displayV2
end LeanFormal.IUT.XiFPaper.Mzk1P6DisplayTermsFinalActual
end
