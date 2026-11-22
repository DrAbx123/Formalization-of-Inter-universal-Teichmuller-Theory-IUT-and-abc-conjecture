import tmp.sheaf.xif.paper.Mzk1P6Thm110DisplayActual
import tmp.sheaf.xif.paper.Mzk1P6PaperBoundActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PaperBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P6IVActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayConsumerActual
theorem p6_display_and_paperBound
    (T : Thm110DisplayTerms) (hl : 7 ≤ T.l) (hd : 1 ≤ T.dmod)
    (hS : 0 ≤ T.logDFpd + T.logFFpd)
    (hE : 0 ≤ T.eStar * T.l + T.etaPrm)
    (hCor312 : thm110Lhs T ≤ thm110Mid T + thm110Cor312Gap T)
    (n : Nat) (hn : 1 ≤ n) (D Q S Tq : ℝ) :
    thm110Lhs T ≤ thm110Rhs T ∧
      p6IVR n D Q S Tq ≤ p6PaperBound n D Q S Tq :=
  ⟨p6_thm110_display T hl hd hS hE hCor312,
    p6IVR_le_paperBound n hn D Q S Tq⟩
#print axioms p6_display_and_paperBound
end LeanFormal.IUT.XiFPaper.Mzk1P6Thm110DisplayConsumerActual
end