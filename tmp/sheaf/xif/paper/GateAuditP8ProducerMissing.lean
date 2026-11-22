/- Gate audit: P8 producer/consumer status and exact missing objects. -/
import tmp.sheaf.xif.paper.P8ProducerMissingExact
import tmp.sheaf.xif.paper.GateAuditNewDone
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.GateAuditP8ProducerMissing
open LeanFormal.IUT.XiFPaper.P8ProducerMissingExact
open LeanFormal.IUT.XiFPaper.GateAuditNewDone

def p8ProducerStatus : String :=
  "producer missing: forall eps>0 Nonempty FreyHeightBound (ABC-level open); consumers accepted; belyiCompactnessToFreyHeight missing"

def gateP8ProducerRows : List String :=
  [ "P8ProducerRecordDone (record/consumers)"
  , "P8HeightAssemblyFixed (consumer)"
  , "P8ProducerAttempt (attempt + missing bridge)"
  , "P8ProducerGateRecord (bridge iff producer)"
  , "P8ConsumerRecordDone (consumer)"
  , "P8ProducerMissingExact (missing list)"
  ]

theorem gateP8ProducerRows_length : gateP8ProducerRows.length = 6 := rfl
theorem missingList_matches : missingObjectsExact.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.GateAuditP8ProducerMissing
end
