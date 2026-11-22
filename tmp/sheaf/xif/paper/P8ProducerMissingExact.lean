/- Exact missing-object record for the P8 producer. -/
import tmp.sheaf.xif.paper.P8ProducerGateRecord
import tmp.sheaf.xif.paper.P8ProducerAttempt
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.P8ProducerMissingExact
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open LeanFormal.IUT.XiFPaper.P8ProducerGateRecord
open LeanFormal.IUT.XiFPaper.P8ProducerAttempt

def missingObjectsExact : List String :=
  [ "FreyHeightBound epsilon producer (forall eps>0, Nonempty (FreyHeightBound eps))"
  , "bridge belyiCompactnessToFreyHeight (compactness -> Frey height)"
  , "actual S2953CThetaUpperCertificate for hCor312"
  ]

theorem missingObjectsExact_length : missingObjectsExact.length = 3 := rfl

theorem producer_iff_bridge :
    (∀ ε : Real, 0 < ε → Nonempty (FreyHeightBound ε)) ↔
      belyiCompactnessToFreyHeight :=
  bridge_iff_producer.symm

#print axioms missingObjectsExact_length
end LeanFormal.IUT.XiFPaper.P8ProducerMissingExact
end
