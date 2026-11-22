/- P5 bridge actual producers: ProductHaarToFiberMult / WeightedQSumBridge
producers built from the actual C_t/G_t/table species and the GREEN realified
q-pilot donor; then the reading equality.  Watchdog only; no interface-only. -/
import tmp.sheaf.xif.paper.Mzk1P5ActualPacketTable
import tmp.sheaf.xif.paper.Mzk1ProductFiberMultBridgeGapActual
import tmp.sheaf.xif.paper.Mzk1P5PacketReadingActual
import tmp.sheaf.xif.paper.Mzk1QVRealifiedBridgeActual
import tmp.sheaf.xif.paper.Node09HqMultConsumerActual
import tmp.sheaf.xif.paper.Mzk1Node0609ProductBridgeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Mzk1P5ActualPacketTable
open LeanFormal.IUT.XiFPaper.Mzk1ProductFiberMultBridgeGapActual
open LeanFormal.IUT.XiFPaper.Mzk1P5PacketReadingActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual
open LeanFormal.IUT.XiFPaper.Mzk1Node0609ProductBridgeActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Actual closed-ball product log sum in the ProductHaarToFiberMult form,
built from the actual qV fiber multiplicities. -/
noncomputable def productLocalLogSum
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real) : Real :=
  (1 / (2 * l)) *
    (∑ i : FinitePlaceAtPrime F p,
      fiberMult X b i / Fdeg * Real.log (residueNormBase (b i).1))

/-- Actual ProductHaarToFiberMult producer: its canonical inhabitant is the
explicit product local log sum (the interface is an equality definition). -/
theorem productHaarToFiberMult_actual
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : Real) :
    ProductHaarToFiberMult X (productLocalLogSum X b Fdeg l) b Fdeg l := rfl

/-- Actual WeightedQSumBridge producer: the realified q-pilot log-volume and the
weight-1 bad-side readout are equal by the GREEN donor. -/
theorem weightedQSumBridge_actual :
    WeightedQSumBridge (qPilotRealifiedLogVolume X) (-MqBad X (fun _ => 1)) :=
  qPilotRealifiedLogVolume_eq_neg_MqBad X

/-- Actual reading equality: the normalized realified log-volume equals the
weight-1 bad-side readout. -/
theorem packetReadingInput_actual :
    PacketReadingInput (qPilotRealifiedLogVolume X) (-MqBad X (fun _ => 1)) :=
  qPilotRealifiedLogVolume_eq_neg_MqBad X

#print axioms productHaarToFiberMult_actual
#print axioms weightedQSumBridge_actual
#print axioms packetReadingInput_actual

end LeanFormal.IUT.XiFPaper.Mzk1P5BridgeProofActual
end
