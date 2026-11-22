/- P6 actual display terms and chain. -/
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual

/-- Actual Thm 1.10 data from the P6 display source dictionary. -/
noncomputable def p6ActualData (D : P6DisplaySourceData) : ActualThm110Data :=
  D.toActualData

/-- Actual display terms from the P6 dictionary. -/
noncomputable def p6ActualTerms (D : P6DisplaySourceData) : Thm110DisplayTerms :=
  D.toTerms

/-- P6 display chain end-to-end. -/
theorem p6Actual_display
    (D : P6DisplaySourceData)
    (hCor312 : thm110Lhs D.toTerms ≤ thm110Mid D.toTerms + thm110Cor312Gap D.toTerms) :
    thm110Lhs D.toTerms ≤ thm110Rhs D.toTerms :=
  p6_display_chain D hCor312

#check p6ActualData
#check p6ActualTerms
#check p6Actual_display
end LeanFormal.IUT.XiFPaper.Mzk1G1P8P6DisplayActual
end
