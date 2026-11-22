/- P5 inequality and carrier glue: signed qReading <= thetaReading from the
accepted paper signed inequality, and the P4-closure-supported P5 q-reading
carrier reading.  No equality between q and theta readings is asserted. -/
import tmp.sheaf.xif.paper.Mzk1P4P5QThetaReadingIntegrationActual
import tmp.sheaf.xif.paper.Mzk1Cor312AcceptedFinalActual
import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import tmp.sheaf.xif.paper.Mzk1P5BridgeProofActual
import tmp.sheaf.xif.paper.Mzk1P5PacketReadingActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P5InequalityCarrierGlueActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadingClosureActual
open LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P4P5QThetaReadingIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PacketReadingActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- P5 signed inequality: qReading <= thetaReading (paper signed form). -/
theorem p5_signed_inequality
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T) :
    R.qReading ≤ R.thetaReading :=
  LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_signed_inequality T R

/-- Strict form of the P5 signed inequality. -/
theorem p5_strict_inequality
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] (R : PaperKummerReading T) :
    R.qReading < R.thetaReading :=
  LeanFormal.IUT.XiFPaper.Mzk1Cor312AcceptedFinalActual.accepted_strict T R

/-- Carrier glue: the P5 q-reading carrier reading is supported by the P4
J_q closure and the actual P5 bridge producer. -/
theorem p5_carrier_qReading_glue :
    PacketReadingInput (qPilotRealifiedLogVolume X)
      (weightedReadout X (fun _ => 1)) :=
  p5_actualQReadingInput X

/-- Carrier glue in the J_q-log form. -/
theorem p5_carrier_jqLog_glue :
    Real.log (jqIndex (X := X) : Real) = -qPilotRealifiedLogVolume X :=
  p4_jqLog_equals_neg_p5_qPilot X

/-- Combined P5 carrier glue: q-reading input plus J_q scalar comparison. -/
theorem p5_carrier_glue :
    PacketReadingInput (qPilotRealifiedLogVolume X)
        (weightedReadout X (fun _ => 1)) ∧
      Real.log (jqIndex (X := X) : Real) =
        -qPilotRealifiedLogVolume X :=
  ⟨p5_carrier_qReading_glue X, p5_carrier_jqLog_glue X⟩

#print axioms p5_signed_inequality
#print axioms p5_strict_inequality
#print axioms p5_carrier_qReading_glue
#print axioms p5_carrier_jqLog_glue
#print axioms p5_carrier_glue

end LeanFormal.IUT.XiFPaper.Mzk1P5InequalityCarrierGlueActual
end
