/- P6 IV display integration: composes the actual P6 Thm 1.10 slack producer
with the S3171 final display; no new paper input is created. -/
import tmp.sheaf.xif.paper.Mzk1P6ActualProducersActual
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1P6ActualProducersActual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayIntegrationActual
/-- P6 actual display inputs: the slack component is the actual producer
`p6_thm110_slack`, not a new hypothesis. -/
def p6DisplayInputsOfCor312
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    Thm110DisplayInputs T :=
  ⟨hCor312, p6_thm110_slack T hl hd hS hE hCor312⟩
/-- P6 IV final display integration: the exact Thm 1.10 display follows
from the actual P6 slack producer and the Cor 3.12 input. -/
theorem p6_iv_final_display
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Lhs T ≤ thm110Rhs T :=
  thm110_final_display T (p6DisplayInputsOfCor312 T hl hd hS hE hCor312)
#print axioms p6DisplayInputsOfCor312
#print axioms p6_iv_final_display
end LeanFormal.IUT.XiFPaper.Mzk1P6IVDisplayIntegrationActual
end