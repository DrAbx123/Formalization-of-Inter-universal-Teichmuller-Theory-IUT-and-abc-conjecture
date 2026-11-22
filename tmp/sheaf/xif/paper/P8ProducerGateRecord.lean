/- Gate record for the missing P8/G1 producer bridge: with the actual G1
compactness data, the bridge is equivalent to the all-epsilon Frey producer. -/
import tmp.sheaf.xif.paper.P8ProducerAttempt
import tmp.sheaf.xif.paper.P8ProducerRecordDone
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ProducerGateRecord
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.P8ProducerAttempt

theorem bridge_iff_producer :
    belyiCompactnessToFreyHeight ↔ (∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)) := by
  constructor
  · intro h
    exact h g1Compactness_actual
  · intro h _
    exact h

theorem producer_of_bridgeDone (h : belyiCompactnessToFreyHeight) :
    ∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε) :=
  bridge_iff_producer.mp h

#print axioms bridge_iff_producer
end LeanFormal.IUT.XiFPaper.P8ProducerGateRecord
end
