/- Gate audit record after the 2026-11-16 new DONE batch. -/
import tmp.sheaf.xif.paper.GateAuditCurrentActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.GateAuditNewDone
open LeanFormal.IUT.XiFPaper.GateAuditCurrentActual

def gateNewDone : List String :=
  [ "P8ProducerRecordDone (record + consumers)"
  , "P8HeightAssemblyFixed (producer record + P6/IV display)"
  , "P8UniformHeightInputFinal (input shape + ABC equivalence)"
  , "ABCBridgeRadicalDone (radical + criterion equivalence)"
  , "GateAuditNewDone (this record)"
  , "P8ProducerAttempt (attempt; exact missing bridge)"
  ]

def gateNewAccepted : List String :=
  [ "G1FermatCoverAssemblyDone (aux)"
  , "G1FermatDifferentBoundDone (aux)"
  , "P6IVPaperBoundWiringChain (wiring)"
  , "P7DownstreamGapAdd (downstream algebra)"
  , "P8FreyProducerConsumer (consumer)"
  , "P6PacketHullPhi (generic Phi)"
  ]

theorem gateNewDone_length : gateNewDone.length = 6 := rfl
theorem gateNewAccepted_length : gateNewAccepted.length = 6 := rfl
theorem gateBaseOpen_length : gateAuditOpenBlockers.length = 5 := rfl
#print axioms gateNewDone_length
end LeanFormal.IUT.XiFPaper.GateAuditNewDone
end
