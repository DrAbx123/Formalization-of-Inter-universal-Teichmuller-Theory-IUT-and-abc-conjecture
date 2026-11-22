import tmp.sheaf.xif.paper.Node09P5ThetaSideFinalActual
import tmp.sheaf.xif.paper.Mzk1P4JqLatticeActual
import Mathlib.Tactic

set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual

namespace LeanFormal.IUT.XiFPaper.Node09P5NodeAssemblyActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S))]
variable [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
  MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
  BorelSpace (qVFamTensorBlock X.S b)]

/-- Actual P5 q-reading: the realified q-pilot log-volume. -/
noncomputable def p5QReading : Real := qPilotRealifiedLogVolume X

/-- Actual P5 theta-reading: direct sum of the per-b qVFam theta-hull logs. -/
noncomputable def p5ThetaReading : Real := qVFamThetaReading X

@[simp] theorem p5QReading_eq :
    p5QReading X = qPilotRealifiedLogVolume X := rfl

@[simp] theorem p5ThetaReading_eq :
    p5ThetaReading X =
      ∑ b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection X.S),
        qVFamLocalThetaHullLogVolume X.S b := rfl

/-- The q-reading is the negative jqIndex log (P4 Jq closure). -/
theorem p5QReading_eq_neg_log_jqIndex :
    p5QReading X = -Real.log (jqIndex (X := X) : Real) :=
  p4_qPilot_eq_neg_log_jqIndex X

/-- P5 signed node: qReading <= thetaReading, with the actual definitions above. -/
theorem p5_qReading_le_thetaReading :
    p5QReading X ≤ p5ThetaReading X :=
  qPilotRealifiedLogVolume_le_thetaReading X

#print axioms p5QReading_eq_neg_log_jqIndex
#print axioms p5_qReading_le_thetaReading

end LeanFormal.IUT.XiFPaper.Node09P5NodeAssemblyActual
end