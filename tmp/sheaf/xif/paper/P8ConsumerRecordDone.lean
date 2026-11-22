/- P8 consumer record: producer record + accepted P6/IV display data. -/
import tmp.sheaf.xif.paper.P8HeightAssemblyFixed
import tmp.sheaf.xif.paper.P8ProducerRecordDone
import tmp.sheaf.xif.paper.P8UniformHeightInputFinal
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ConsumerRecordDone
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.P8ProducerRecordDone
open LeanFormal.IUT.XiFPaper.P8HeightAssemblyFixed
open LeanFormal.IUT.XiFPaper.P8UniformHeightInputFinal

theorem consumerRecord_combined (A : ActualThm110Data) (c : Real)
    (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (P : P8ProducerRecordDone) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8HeightAssembly_fixed A c D hCor312 P

theorem consumerRecord_input (P : P8ProducerRecordDone) :
    P8UniformHeightInputFinal :=
  producer_to_inputFinal P

#print axioms consumerRecord_combined
#print axioms consumerRecord_input
end LeanFormal.IUT.XiFPaper.P8ConsumerRecordDone
end
