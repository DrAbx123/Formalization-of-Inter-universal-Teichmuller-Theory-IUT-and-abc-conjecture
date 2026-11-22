/- Small: q reading = -M and M = Q/(2l). -/
import tmp.sheaf.xif.paper.Mzk1QVRealifiedBridgeActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P6P5QReadingNegM2
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]
theorem qReading_eq_negM :
    LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual.qPilotRealifiedLogVolume X =
      -MqBad X (fun _ => 1) :=
  LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual.qPilotRealifiedLogVolume_eq_neg_MqBad X
noncomputable def paperQFromM (M : Real) : Real := 2 * (l.value : Real) * M
theorem M_eq_Q_div_two_l (M : Real) :
    M = paperQFromM (l := l) M / (2 * (l.value : Real)) := by
  unfold paperQFromM
  have hl : (2 * (l.value : Real)) ≠ 0 := by
    have h : (0 : Real) < (l.value : Real) := by exact_mod_cast l.prime.pos
    linarith
  field_simp [hl]
  ring
#check qReading_eq_negM
#check paperQFromM
#check M_eq_Q_div_two_l
end LeanFormal.IUT.XiFPaper.Mzk1P6P5QReadingNegMActual
end
