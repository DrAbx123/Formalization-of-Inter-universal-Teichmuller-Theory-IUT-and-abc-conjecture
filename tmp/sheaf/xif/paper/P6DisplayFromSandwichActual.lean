/- P6 display from P5 sandwich: no S2953 extra coefficient premise. -/
import tmp.sheaf.xif.paper.Mzk1P6HCor312ActualFromP5Actual
import tmp.sheaf.xif.paper.Mzk1P6DisplayDictionaryActual
import tmp.sheaf.xif.paper.Mzk1P6HCor312SupplyFromP5Actual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P6DisplayFromSandwichActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6DisplayDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1P6HCor312ActualFromP5Actual
open LeanFormal.IUT.XiFPaper.Mzk1P6HCor312SupplyFromP5Actual
/-- P6 display chain using the P5-supplied hCor312 input (no S2953 coefficient premise). -/
theorem p6DisplayFromSandwich (D : P6DisplaySourceData)
    (hCor312 : S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Mid D.toTerms +
        S3171IUTIVSection1DisplayActual.thm110Cor312Gap D.toTerms) :
    S3171IUTIVSection1DisplayActual.thm110Lhs D.toTerms ≤
      S3171IUTIVSection1DisplayActual.thm110Rhs D.toTerms :=
  p6_display_chain D hCor312
/-- Exposed accepted P5 local volume inequality used by the sandwich route. -/
noncomputable def p5SandwichInput := Mzk1P6HCor312SupplyFromP5Actual.p5_local_volume_inequality
#check p6DisplayFromSandwich
#check p5SandwichInput
end LeanFormal.IUT.XiFPaper.P6DisplayFromSandwichActual
end
