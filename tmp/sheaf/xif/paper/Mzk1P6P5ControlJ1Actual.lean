/- J1 core: P5 theta reading = 0 <= H_pkt = 0, and q_P5 = -M with M=Q/(2l). -/
import tmp.sheaf.xif.paper.Node09P5ThetaReadingZeroActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.Mzk1QVRealifiedBridgeActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P6P5ControlJ1Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Node09P5ThetaReadingZeroActual
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [∀ b : Bad (nativePlaceSelection X.S),
  MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (nativePlaceSelection X.S),
  BorelSpace (qVFamTensorBlock X.S b)]

/-- P5 theta reading is zero. -/
theorem thetaReading_zero : qVFamThetaReading X = 0 :=
  qVFamThetaReading_eq_zero X

/-- Weighted packet theta hull volume is zero. -/
theorem Hpkt_zero : globalQVFamThetaHullLog X.S = 0 := by
  unfold globalQVFamThetaHullLog
  apply Finset.sum_eq_zero
  intro b _
  rw [qVFamLocalThetaHullLogVolume_eq_zero X.S b]
  ring

/-- Theta_P5 <= H_pkt. -/
theorem thetaP5_le_Hpkt : qVFamThetaReading X ≤ globalQVFamThetaHullLog X.S := by
  rw [thetaReading_zero X, Hpkt_zero X]

/-- q reading = -M for actual M. -/
theorem qP5_eq_negM :
    LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X =
      -MqBad X (fun _ => 1) :=
  LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual.qPilotRealifiedLogVolume_eq_neg_MqBad X

/-- Paper Q from M: Q = 2*l*M. -/
noncomputable def paperQFromM (M : Real) : Real := 2 * (l.value : Real) * M

/-- M = Q/(2l) for Q = 2*l*M. -/
theorem M_eq_Q_div_two_l (M : Real) :
    M = paperQFromM (l := l) M / (2 * (l.value : Real)) := by
  unfold paperQFromM
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    have h : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  have hl1 : (l.value : Real) ≠ 0 := by
    exact_mod_cast l.prime.ne_zero
  field_simp [hl]

/-- C2 data: q_P5=-M, theta_P5<=H_pkt, M=Q/(2l). -/
structure C2Data where
  M : Real
  Q : Real
  qP5 : Real
  thetaP5 : Real
  Hpkt : Real
  qP5_eq : qP5 = -M
  qP5_def : qP5 =
    LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X
  thetaP5_le : thetaP5 ≤ Hpkt
  M_eq_Q : M = Q / (2 * (l.value : Real))

noncomputable def c2Data : C2Data X where
  M := MqBad X (fun _ => 1)
  Q := paperQFromM (l := l) (MqBad X (fun _ => 1))
  qP5 := LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X
  thetaP5 := qVFamThetaReading X
  Hpkt := globalQVFamThetaHullLog X.S
  qP5_eq := by
    rw [qP5_eq_negM X]
  qP5_def := rfl
  thetaP5_le := thetaP5_le_Hpkt X
  M_eq_Q := M_eq_Q_div_two_l (MqBad X (fun _ => 1))

#check thetaReading_zero
#check Hpkt_zero
#check thetaP5_le_Hpkt
#check qP5_eq_negM
#check c2Data

end LeanFormal.IUT.XiFPaper.Mzk1P6P5ControlJ1Actual
end
