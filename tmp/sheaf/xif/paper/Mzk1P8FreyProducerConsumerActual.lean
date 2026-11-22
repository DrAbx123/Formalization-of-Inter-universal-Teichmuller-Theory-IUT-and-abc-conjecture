/- P8 consumer from the producer record: Frey producer -> P8 bound -> combined
display/ABC consumer with the accepted P6/IV data. -/
import tmp.sheaf.xif.paper.Mzk1P8ProducerRecordActual
import tmp.sheaf.xif.paper.Mzk1P8FromP6IVActual
import tmp.sheaf.xif.paper.Mzk1P8UniformHeightBoundProducerDoneActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8FreyProducerConsumerActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ProducerRecordActual
open LeanFormal.IUT.XiFPaper.Mzk1P8UniformHeightBoundProducerDoneActual
theorem p8ProducerRecord_bound (D : P8ProducerRecord) : P8UniformHeightBound :=
  p8FreyProducer_bound D.freyHeight
theorem p8ProducerRecord_combined (A : ActualThm110Data) (c : Real)
    (D : P8FromP6IVData A c)
    (hCor312 : thm110Lhs A.toTerms ≤ thm110Mid A.toTerms + thm110Cor312Gap A.toTerms)
    (P : P8ProducerRecord) :
    thm110Lhs (p8ActualDisplayTerms A) ≤ thm110Rhs (p8ActualDisplayTerms A) ∧
      ABCConjecture :=
  p8FromP6IV_combined A c D hCor312 (p8ProducerRecord_bound P)
#print axioms p8ProducerRecord_bound
#print axioms p8ProducerRecord_combined
end LeanFormal.IUT.XiFPaper.Mzk1P8FreyProducerConsumerActual
end
