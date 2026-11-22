/- Record of producer-record -> criterionAll -> ABCStatement chain. -/
import tmp.sheaf.xif.paper.Mzk1P8ProducerRecordActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerChainRecordActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ProducerRecordActual
theorem producerChain_abcStatement (D : P8ProducerRecord) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (p8ProducerRecord_criterionAll D)
#print axioms producerChain_abcStatement
end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerChainRecordActual
end
