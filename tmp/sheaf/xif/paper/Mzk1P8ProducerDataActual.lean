/- P8 producer data packaging: Frey height data for all epsilon separately from
its consumer to ABC and to the P8 uniform height bound. -/
import tmp.sheaf.xif.paper.Mzk1G1FreyHeightActual
import tmp.sheaf.xif.paper.Mzk1G1EllipticHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P8ProducerDataActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual

/-- P8 producer data: for every epsilon a Frey height bound. -/
structure P8ProducerData where
  freyHeight : ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)

theorem producerData_criterionAll (D : P8ProducerData) :
    ABCEllipticHeightCriterionAll :=
  freyHeightBoundAll_iff_criterionAll.mp D.freyHeight

theorem producerData_abcStatement (D : P8ProducerData) : ABCStatement :=
  abcStatement_of_ellipticHeightCriterion (producerData_criterionAll D)

#print axioms producerData_criterionAll
#print axioms producerData_abcStatement
end LeanFormal.IUT.XiFPaper.Mzk1P8ProducerDataActual
end
