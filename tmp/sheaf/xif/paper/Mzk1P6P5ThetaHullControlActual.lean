/- CORE P6 path: P5 theta reading control and q reading = -M, M=Q/(2l). -/
import tmp.sheaf.xif.paper.Node09P5ThetaSideFinalActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.Mzk1QVRealifiedBridgeActual
import tmp.sheaf.xif.paper.Mzk1P5P6ReadingChainActual
import Mathlib.Tactic

set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControlActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Node09P5ThetaSideFinalActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P5P6ReadingChainActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [∀ b : Bad (nativePlaceSelection X.S),
  MeasurableSpace (qVFamTensorBlock X.S b)]
variable [∀ b : Bad (nativePlaceSelection X.S),
  BorelSpace (qVFamTensorBlock X.S b)]

/-- P5 theta reading is the direct sum of local theta-hull volumes. -/
theorem thetaReading_eq_sum :
    qVFamThetaReading X =
      ∑ b : Bad (nativePlaceSelection X.S), qVFamLocalThetaHullLogVolume X.S b := rfl

/-- The q reading is -M for the actual weighted q sum. -/
theorem qReading_eq_neg_M :
    LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X =
      -MqBad X (fun _ => 1) :=
  LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual.qPilotRealifiedLogVolume_eq_neg_MqBad X

/-- Paper Q from M: Q = 2*l*M, equivalently M = Q/(2l). -/
noncomputable def paperQFromM (M : Real) : Real := 2 * (l.value : Real) * M

theorem paperM_eq_paperQ_div_two_l (M : Real) :
    M = paperQFromM (l := l) M / (2 * (l.value : Real)) := by
  unfold paperQFromM
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    have h : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  field_simp [hl]

/-- P5 theta reading controlled by the weighted theta hull volume. -/
theorem thetaReading_le_weightedHull :
    qVFamThetaReading X ≤ globalQVFamThetaHullLog X.S := by
  unfold qVFamThetaReading globalQVFamThetaHullLog
  apply Finset.sum_le_sum
  intro b _
  linarith

#check thetaReading_eq_sum
#check qReading_eq_neg_M
#check paperM_eq_paperQ_div_two_l
#check thetaReading_le_weightedHull

end LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControlActual
end
