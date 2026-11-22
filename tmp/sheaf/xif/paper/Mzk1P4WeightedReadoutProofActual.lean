/- P4 actual weighted-readout proof: repeated-factor weighted equality for the
bad-side q readout, proved from the GREEN realified donor
`qPilotRealifiedLogVolume_eq_neg_MqBad`.  No interface-only data is used. -/
import tmp.sheaf.xif.paper.Mzk1QVRealifiedBridgeActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Bad-side weighted q readout: negative of the weighted multiplicity sum. -/
noncomputable def weightedReadout
    (w : Bad (nativePlaceSelection X.S) → Real) : Real :=
  -MqBad X w

/-- Repeated-factor pull-out: a constant weight `c` on every bad factor pulls
out of the weighted sum. -/
theorem MqBad_const_weight (c : Real) :
    MqBad X (fun _ => c) = c * MqBad X (fun _ => 1) := by
  unfold MqBad
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [one_mul]
  ring

/-- Weight-1 readout is exactly the realified q-pilot log-volume (GREEN donor). -/
theorem weightedReadout_one_eq_logVolume :
    weightedReadout X (fun _ => 1) = qPilotRealifiedLogVolume X := by
  unfold weightedReadout
  rw [qPilotRealifiedLogVolume_eq_neg_MqBad]

/-- Repeated-factor weighted equality: the readout with the same weight `c`
repeated on all bad factors equals `c` times the realified q-pilot log-volume. -/
theorem weightedReadout_repeated_factor_eq_logVolume (c : Real) :
    weightedReadout X (fun _ => c) = c * qPilotRealifiedLogVolume X := by
  unfold weightedReadout
  rw [MqBad_const_weight, qPilotRealifiedLogVolume_eq_neg_MqBad]
  ring

/-- The same equality in `MqBad` form. -/
theorem MqBad_repeated_factor_eq_neg_logVolume (c : Real) :
    MqBad X (fun _ => c) = -c * qPilotRealifiedLogVolume X := by
  rw [MqBad_const_weight, qPilotRealifiedLogVolume_eq_neg_MqBad]
  ring

#print axioms MqBad_const_weight
#print axioms weightedReadout_one_eq_logVolume
#print axioms weightedReadout_repeated_factor_eq_logVolume
#print axioms MqBad_repeated_factor_eq_neg_logVolume

end LeanFormal.IUT.XiFPaper.Mzk1P4WeightedReadoutProofActual
end
