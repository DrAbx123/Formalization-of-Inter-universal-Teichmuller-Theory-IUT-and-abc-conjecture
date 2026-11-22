import tmp.sheaf.xif.paper.S2726C3ComparisonRegionRhoActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.xif.paper.S2721BridgeSkeletonActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

namespace LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual

/-- TARGET (not compiled): rho index bridge between the C3 tensor index and
the native bad-place family.  This is the exact index datum needed to feed the
tensor comparison region from a native source. -/
def S2726TensorIndexBridgeTarget
    {l : PrimeGeFive} {V : Type} {I : OriginalInput.{0, 0, 0, 0, 0} l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (C3.tensorIndex ≃ Bad (nativePlaceSelection T))

end LeanFormal.IUT.XiFPaper.S2726TensorComparisonRegionRhoActual
end
