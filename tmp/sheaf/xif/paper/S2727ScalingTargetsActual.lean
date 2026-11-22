import tmp.sheaf.xif.paper.C3LambdaONormalizedScalarActual
import tmp.sheaf.xif.paper.S2727V2RegionTarget
import tmp.sheaf.xif.paper.S2727V2AssemblyActual
import LeanFormal.IUT.ABCBridge.Statement
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.C3LambdaONormalizedScalarActual
open LeanFormal.IUT.XiFPaper.S2726C3PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2727V2RegionTarget
open LeanFormal.IUT.XiFPaper.S2727V2AssemblyActual
namespace LeanFormal.IUT.XiFPaper.S2727ScalingTargetsActual
variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (lam : HullBlock C3)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

/-- The actual λ-scaled comparison region λ·O of the C3 log-shell tensor. -/
abbrev S2727ScaledRegion : Set (C3LogShellTensorBlock C3) :=
  actualScaledRegion C3 lam

/-- Its actual Haar log-volume. -/
abbrev S2727ScaledRegionVolume : Real :=
  (c3ScaledHaar C3 lam).toReal

/-- Exact scaling formula: scaled volume = scalingRatio * unit volume. -/
theorem S2727ScaledRegionVolume_eq_scalingRatio_mul_unit
    (N : C3LambdaONormalizationData C3 lam) :
    S2727ScaledRegionVolume C3 lam =
      N.scalingRatio * (c3UnitHaar C3).toReal := by
  unfold S2727ScaledRegionVolume
  rw [N.scalingRatio_eq]
  exact (div_mul_cancel₀ (c3ScaledHaar C3 lam).toReal
    (ne_of_gt (ENNReal.toReal_pos N.unit_measure_pos.ne'
      N.unit_measure_lt_top.ne))).symm

/-- Exact actual hheight shape on λ·O, with additive constant A(ε). -/
def S2727HheightTargetScaled (A : Real → Real) : Prop :=
  ∀ (eps : Real), 0 < eps →
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + eps) * S2727ScaledRegionVolume C3 lam + A eps

/-- Exact actual hvol shape on λ·O, with hull log-volume theta bound + D. -/
def S2727HvolTargetScaled : Prop :=
  ∀ (eps : Real), 0 < eps →
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      S2727ScaledRegionVolume C3 lam ≤
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          ((S2727C3HullData C3).logVolume
            (S2727C3HullData C3).hull).toReal + D

#check S2727ScaledRegion
#check S2727ScaledRegionVolume
#check S2727ScaledRegionVolume_eq_scalingRatio_mul_unit
#check S2727HheightTargetScaled
#check S2727HvolTargetScaled
#print axioms S2727ScaledRegionVolume_eq_scalingRatio_mul_unit

end LeanFormal.IUT.XiFPaper.S2727ScalingTargetsActual