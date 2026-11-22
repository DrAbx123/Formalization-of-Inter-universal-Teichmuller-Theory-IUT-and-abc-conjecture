import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1QVMultiplicityBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
variable {l : PrimeGeFive} (X : N8NativeInput l)
/-- The q_v effective multiplicity is exactly `order(q_v) * local residue degree`;
this is the multiplicity that must be carried into `RamifiedPlaceData.mult`.
It preserves the vanishing order, not merely the residue degree. -/
theorem qVEffectiveMultiplicity_eq_order_mul_localResidueDegree
    (b : Bad (nativePlaceSelection X.S)) :
    (qVEffectiveMultiplicity X b : ℝ) =
      ((qVFamily X.S b).order : ℝ) *
        (localResidueDegree (k := X.S.arithmetic.Fmod) ((nativeBadLift X.S).lift b) : ℝ) := by
  unfold qVEffectiveMultiplicity
  push_cast
  ring
#check qVEffectiveMultiplicity_eq_order_mul_localResidueDegree
end LeanFormal.IUT.XiFPaper.Mzk1QVMultiplicityBridgeActual
end