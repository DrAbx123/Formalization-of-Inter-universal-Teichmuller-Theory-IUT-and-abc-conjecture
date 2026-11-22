/- P6 display final: exact Thm 1.10 display from the actual display chain. -/
import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6DisplayFinalActual
theorem p6_display_final
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Lhs T ≤ thm110Rhs T :=
  p6_thm110_display T hl hd hS hE hCor312
#print axioms p6_display_final
end LeanFormal.IUT.XiFPaper.Mzk1P6DisplayFinalActual
end