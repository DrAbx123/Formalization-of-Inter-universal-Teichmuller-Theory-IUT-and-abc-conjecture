/- P6 actual Thm 1.10 display chain from the S3171 display and constants. -/
import tmp.sheaf.xif.paper.S3171IUTIVSection1DisplayActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
/-- Actual display terms from the P6 display constants. -/
def p6Thm110Terms
    (l dmod logDFpd logFFpd eStar etaPrm logQ : Real) : Thm110DisplayTerms :=
  { l := l, dmod := dmod, logDFpd := logDFpd, logFFpd := logFFpd,
    eStar := eStar, etaPrm := etaPrm, logQ := logQ }
/-- Actual P6 display inputs: the slack is derived by the S3171 Step (v) producer. -/
def p6Thm110Inputs
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    Thm110DisplayInputs T :=
  Thm110DisplayInputsOfCor312 T hl hd hS hE hCor312
/-- Actual P6 Thm 1.10 final display. -/
theorem p6_thm110_display
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T) :
    thm110Lhs T ≤ thm110Rhs T :=
  thm110_final_display T (p6Thm110Inputs T hl hd hS hE hCor312)
#print axioms p6Thm110Terms
#print axioms p6Thm110Inputs
#print axioms p6_thm110_display
end LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
end