/- P8 chain from accepted P6/IV display data and the Frey producer: display
slack plus ABC. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVChainDoneActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual

theorem p8Chain_of_frey (h : ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)) :
    P8UniformHeightBound :=
  p8UniformHeightBound_iff_abc.mpr
    (ABCStatementBridgeActual.abcStatement_to_ABCConjecture
      (abcStatement_of_ellipticHeightCriterion (freyHeightBoundAll_iff_criterionAll.mp h)))

theorem p8Chain_combined (A : ActualThm110Data) (c : Real) (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8FromP6IV_combined A c D hCor312 (p8Chain_of_frey h)
#print axioms p8Chain_combined
end LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVChainDoneActual
end
