/- P4 -> P5 integration: use the P4 J_q closure to support the actual P5
q-reading.  The P5 theta-side measure reading is recorded separately in
Mzk1P5ReadingProofActual; this file avoids overlapping the H1a/H1b
hull/lattice work. -/
import tmp.sheaf.xif.paper.Mzk1P4WeightedReadingClosureActual
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadingClosureActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PacketReadingActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P4P5QThetaReadingIntegrationActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- P4 closure, read as the actual P5 q-pilot scalar equality. -/
theorem p4_qPilot_eq_neg_log_jqIndex :
    qPilotRealifiedLogVolume X = -Real.log (jqIndex (X := X) : Real) := by
  rw [log_jqIndex_eq_qPilotRealifiedLogVolume (X := X)]
  ring

/-- P4 closure, read as the weight-1 bad readout equality. -/
theorem p4_weightedReadout_eq_neg_log_jqIndex :
    weightedReadout X (fun _ => 1) = -Real.log (jqIndex (X := X) : Real) := by
  rw [weightedReadout_one_eq_logVolume (X := X),
    log_jqIndex_eq_qPilotRealifiedLogVolume (X := X)]
  ring

/-- The actual P5 q-reading input, supported by the P4 closure. -/
theorem p5_actualQReadingInput :
    PacketReadingInput (qPilotRealifiedLogVolume X)
      (weightedReadout X (fun _ => 1)) := by
  simpa only [weightedReadout] using packetReadingInput_actual (X := X)

/-- The P4 J_q scalar is exactly the P5 q-pilot readout; this is the
q-reading support consumed by P5. -/
theorem p4_jqLog_equals_neg_p5_qPilot :
    Real.log (jqIndex (X := X) : Real) = -qPilotRealifiedLogVolume X :=
  log_jqIndex_eq_qPilotRealifiedLogVolume (X := X)

/-- Integrated P4 -> P5 support theorem: the P4 J_q closure yields the P5
q-pilot scalar equality and the P5 q-reading input. -/
theorem p4p5_qReading_supported :
    qPilotRealifiedLogVolume X = -Real.log (jqIndex (X := X) : Real) ∧
      Real.log (jqIndex (X := X) : Real) = -qPilotRealifiedLogVolume X ∧
      PacketReadingInput (qPilotRealifiedLogVolume X)
        (weightedReadout X (fun _ => 1)) :=
  ⟨p4_qPilot_eq_neg_log_jqIndex X,
    p4_jqLog_equals_neg_p5_qPilot X,
    p5_actualQReadingInput X⟩

#print axioms p4_qPilot_eq_neg_log_jqIndex
#print axioms p4_weightedReadout_eq_neg_log_jqIndex
#print axioms p5_actualQReadingInput
#print axioms p4p5_qReading_supported

end LeanFormal.IUT.XiFPaper.Mzk1P4P5QThetaReadingIntegrationActual
end
