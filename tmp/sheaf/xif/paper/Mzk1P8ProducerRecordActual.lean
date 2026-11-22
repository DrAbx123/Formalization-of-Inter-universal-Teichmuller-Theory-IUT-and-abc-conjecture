/- Record of the exact P8 producer input shape (all-epsilon Frey data). -/
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerRecordActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
structure P8ProducerRecord where
  freyHeight : ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)
theorem p8ProducerRecord_criterionAll (D : P8ProducerRecord) :
    ABCEllipticHeightCriterionAll :=
  freyHeightBoundAll_iff_criterionAll.mp D.freyHeight
#print axioms p8ProducerRecord_criterionAll
end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerRecordActual
end
