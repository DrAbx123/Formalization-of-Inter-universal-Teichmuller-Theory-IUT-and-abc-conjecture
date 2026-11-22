/- Final P8 consumer: producer record plus P6/IV input wire. -/
import tmp.sheaf.xif.paper.P8ConsumerRecordDone
import tmp.sheaf.xif.paper.P8ProducerGateRecord
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ConsumerCombinedDoneFinal
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1IVThm110Actual
open LeanFormal.IUT.XiFPaper.S3171IUTIVSection1DisplayActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1P8FromP6IVActual
open LeanFormal.IUT.XiFPaper.P8ProducerRecordDone
open LeanFormal.IUT.XiFPaper.P8ConsumerRecordDone
open LeanFormal.IUT.XiFPaper.P8ProducerGateRecord
theorem final_record_ABC (P : P8ProducerRecordDone) : ABCConjecture :=
  record_ABCConjecture P
theorem final_record_bound (P : P8ProducerRecordDone) : P8UniformHeightBound :=
  record_bound P
#print axioms final_record_ABC
end LeanFormal.IUT.XiFPaper.P8ConsumerCombinedDoneFinal
end
