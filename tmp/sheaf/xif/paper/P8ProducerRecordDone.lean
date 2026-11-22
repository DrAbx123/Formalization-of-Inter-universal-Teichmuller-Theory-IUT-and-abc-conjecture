/- P8 producer record: the exact remaining producer shape and its consumers.
All theorems take the record as input (consumer/conversion; not a producer). -/
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.ABCStatementBridgeActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ProducerRecordDone
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual
open LeanFormal.IUT.XiFPaper.ABCStatementBridgeActual

/-- Exact remaining P8 producer record: all-epsilon Frey height data. -/
structure P8ProducerRecordDone where
  freyHeight : ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)

theorem record_criterionAll (D : P8ProducerRecordDone) :
    ABCEllipticHeightCriterionAll :=
  freyHeightBoundAll_iff_criterionAll.mp D.freyHeight
theorem record_abcStatement (D : P8ProducerRecordDone) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (record_criterionAll D)
theorem record_ABCConjecture (D : P8ProducerRecordDone) : ABCConjecture :=
  ABCStatementBridgeActual.abcStatement_to_ABCConjecture (record_abcStatement D)
theorem record_bound (D : P8ProducerRecordDone) : P8UniformHeightBound :=
  p8UniformHeightBound_iff_abc.mpr (record_ABCConjecture D)
#print axioms record_criterionAll
#print axioms record_bound
end LeanFormal.IUT.XiFPaper.P8ProducerRecordDone
end
