/- P8 FromP6IV data: nonempty data, display slack and combined consumers. -/
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVNonemptyDoneActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual

theorem p8Data_nonempty (A : ActualThm110Data) (c : Real) :
    Nonempty (P8FromP6IVData A c) := p8FromP6IVData_nonempty A c

theorem p8Data_displaySlack (A : ActualThm110Data)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) :=
  p8FromP6IV_displaySlack A hCor312

theorem p8Data_combined (A : ActualThm110Data) (c : Real) (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (h : P8UniformHeightBound) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8FromP6IV_combined A c D hCor312 h
#print axioms p8Data_nonempty
#print axioms p8Data_combined
end LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVNonemptyDoneActual
end
