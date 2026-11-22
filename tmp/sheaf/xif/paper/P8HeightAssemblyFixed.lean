/- Fixed P8 height assembly: producer record + accepted P6/IV display data.
Input-based (record is a hypothesis), no fake. -/
import tmp.sheaf.xif.paper.P8ProducerRecordDone
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8HeightAssemblyFixed
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.P8ProducerRecordDone

theorem p8HeightAssembly_fixed (A : ActualThm110Data) (c : Real)
    (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (P : P8ProducerRecordDone) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8FromP6IV_combined A c D hCor312 (record_bound P)
#print axioms p8HeightAssembly_fixed
end LeanFormal.IUT.XiFPaper.P8HeightAssemblyFixed
end
