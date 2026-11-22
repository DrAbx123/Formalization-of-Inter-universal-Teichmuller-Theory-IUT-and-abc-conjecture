import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

noncomputable section
open LeanFormal.IUT
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2607HeightUpperTargetActualAdapted

universe u

variable {X : Type u}
variable (W : IQHullLogVolumeInterface X)
variable (logShellPoint : Nat -> Nat -> Nat -> X)

/-- **IUT IV §2 gap 1 target, per ABC triple.**  The canonical height is
bounded by `(1+eps)` times the comparison-region log-volume plus `A`. -/
def HeightUpperTarget (eps A : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c) <=
      (1 + eps) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal + A

/-- **IUT IV §2 gap 2 target, per ABC triple.**  The comparison-region
log-volume is bounded by `(1+eps)` times the arithmetic weight, plus the
hull bound and a residual `D`. -/
def RegionVolumeWeightTarget (eps D : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- Combining the two per-triple targets gives the paper-format
`(1+eps)^2` height/weight bound with the constant `(1+eps)*(hull+D)+A`. -/
theorem height_le_sq_weight_of_targets
    {eps A D : Real}
    (hHeight : HeightUpperTarget W logShellPoint eps A)
    (hVolume : RegionVolumeWeightTarget W logShellPoint eps D) :
    forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + eps) * ((1 + eps) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D) + A := by
  intro a b c habc
  have hh := hHeight a b c habc
  have hv := hVolume a b c habc
  nlinarith [hHeight a b c habc, hVolume a b c habc]

/-- **Target-to-contract wiring.**  If for every `eps > 0` the two gap targets
hold with constants `Aeps eps` and `Deps eps`, then the IUT IV Theorem A /
Corollary 2.3 additive height contract `ABCHeightWeightAdditiveBoundV2` holds. -/
theorem ABCHeightWeightAdditiveBoundV2_of_gapTargets
    (Aeps Deps : Real -> Real)
    (hHeight : forall eps : Real, 0 < eps -> HeightUpperTarget W logShellPoint eps (Aeps eps))
    (hVolume : forall eps : Real, 0 < eps -> RegionVolumeWeightTarget W logShellPoint eps (Deps eps)) :
    ABCHeightWeightAdditiveBoundV2 := by
  refine abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive W Aeps ?_
  intro eps heps
  exact
    { logShellPoint := logShellPoint
      height_le_normalizedRegionVolume_add := hHeight eps heps
      regionVolume_le_normalizedWeight := by
        refine ⟨Deps eps, ?_⟩
        intro a b c habc
        exact hVolume eps heps a b c habc }

/-- The per-eps ABC contract from the two gap targets. -/
theorem abcHeightWeightAdditiveBoundV2_of_gapTargets'
    (Aeps Deps : Real -> Real)
    (hHeight : forall eps : Real, 0 < eps -> HeightUpperTarget W logShellPoint eps (Aeps eps))
    (hVolume : forall eps : Real, 0 < eps -> RegionVolumeWeightTarget W logShellPoint eps (Deps eps)) :
    forall eps : Real, 0 < eps -> exists A : Real,
      forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c) <=
          (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A :=
  ABCHeightWeightAdditiveBoundV2.exists_constant
    (ABCHeightWeightAdditiveBoundV2_of_gapTargets W logShellPoint Aeps Deps hHeight hVolume)

#print axioms height_le_sq_weight_of_targets
#print axioms ABCHeightWeightAdditiveBoundV2_of_gapTargets
#print axioms abcHeightWeightAdditiveBoundV2_of_gapTargets'

end LeanFormal.IUT.XiFPaper.S2607HeightUpperTargetActualAdapted
end
