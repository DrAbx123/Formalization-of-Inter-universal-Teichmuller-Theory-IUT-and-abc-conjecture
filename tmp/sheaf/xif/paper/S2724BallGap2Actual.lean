import tmp.sheaf.xif.paper.S2722Gap2AssemblyActual
import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import tmp.sheaf.xif.paper.S2588RationalPointMapActual
import Mathlib.Topology.MetricSpace.Basic

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
open LeanFormal.IUT.XiFPaper.S2722Gap2AssemblyActual
open MeasureTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2724BallGap2Actual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

/-- Ball-thickened comparison region. -/
noncomputable def S2724BallRegion
    (rho : Nat -> Nat -> Nat -> Real) (a n c : Nat) :
    Set (qVFamTensorBlock T b) :=
  (S2586IQHullLogVolumeInterface (l := l) T b).scaleShift ''
    ((S2586IQHullLogVolumeInterface (l := l) T b).unitRegion ∪
      Metric.closedBall (S2588PointMap (l := l) T b a n c) (rho a n c))

/-- Conditional gap-2 target for the ball-thickened region. -/
def S2724BallGap2Target (eps : Real)
    (rho : Nat -> Nat -> Nat -> Real) : Prop :=
  exists D : Real, forall a n c : Nat, IsABCTriple a n c ->
    ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      (S2724BallRegion (l := l) T b rho a n c)).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
        ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
          (S2586IQHullLogVolumeInterface (l := l) T b).hull).toReal + D

/-- Corrected point bound for the ball center, without hval. -/
def S2724BallCenterPointBound (eps : Real) : Prop :=
  forall a n c : Nat, IsABCTriple a n c ->
    ((S2586IQHullLogVolumeInterface (l := l) T b).logVolume
      {(S2586IQHullLogVolumeInterface (l := l) T b).scaleShift
        (S2588PointMap (l := l) T b a n c)}).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c)

#check S2724BallRegion
#check S2724BallGap2Target
#check S2724BallCenterPointBound

end LeanFormal.IUT.XiFPaper.S2724BallGap2Actual
end
