import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1QVFiberWeightedActual
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QVFiberWeightedActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
variable [Fintype (Bad (nativePlaceSelection X.S))]
variable [DecidableEq (FinitePlaceAtPrime F p)]
/-- Bad-side weighted q sum, using the actual realified divisor multiplicities. -/
noncomputable def MqBad (w : Bad (nativePlaceSelection X.S) → Real) : Real :=
  ∑ b : Bad (nativePlaceSelection X.S),
    w b * (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1)
/-- §9.1 route: the realified q-pilot log-volume is exactly the weighted bad-side sum.
This uses the GREEN realified divisor/log-volume donor and needs no S2135 alignment. -/
theorem qPilotRealifiedLogVolume_eq_neg_MqBad :
    qPilotRealifiedLogVolume X = -MqBad X (fun _ => 1) := by
  rw [qPilotRealifiedLogVolume_eq]
  unfold MqBad
  simp only [one_mul]
/-- §9.1 route: the same realified log-volume as the negative fiber-weighted q sum,
via the already-GREEN fiber reindex bridge.  No S2135 prime alignment is used. -/
theorem qPilotRealifiedLogVolume_eq_neg_fiberWeighted
    (idx : Bad (nativePlaceSelection X.S) → FinitePlaceAtPrime F p)
    (logBase : FinitePlaceAtPrime F p → Real)
    (hlog : ∀ b : Bad (nativePlaceSelection X.S),
      Real.log (residueNormBase b.1) = logBase (idx b)) :
    qPilotRealifiedLogVolume X =
      -∑ i : FinitePlaceAtPrime F p, fiberMultWeighted X idx i * logBase i := by
  rw [qPilotRealifiedLogVolume_eq]
  rw [← MqFiberBadSumBridge_of_logBridge X idx logBase hlog]
#check MqBad
#check qPilotRealifiedLogVolume_eq_neg_MqBad
#check qPilotRealifiedLogVolume_eq_neg_fiberWeighted
end LeanFormal.IUT.XiFPaper.Mzk1QVRealifiedBridgeActual
end