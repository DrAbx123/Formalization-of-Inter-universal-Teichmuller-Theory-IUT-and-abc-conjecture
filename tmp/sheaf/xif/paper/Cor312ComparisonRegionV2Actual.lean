import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
noncomputable section
open LeanFormal.IUT
universe u
namespace LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

/-- V2 per-epsilon comparison data: the comparison region is an explicit
point-dependent field, with the shell point contained in it. -/
structure Cor312EpsilonArithmeticComparisonV2 {X : Type u}
    (W : IQHullLogVolumeInterface X) (epsilon : Real) where
  comparisonRegion : Nat → Nat → Nat → Set X
  logShellPoint : Nat → Nat → Nat → X
  logShellPoint_mem :
    ∀ a b c : Nat, logShellPoint a b c ∈ comparisonRegion a b c
  height_le_comparisonRegionVolume :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (W.logVolume (comparisonRegion a b c)).toReal
  regionVolume_le_normalizedWeight :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D

/-- V2 bridge interface, with explicit point-dependent comparison regions. -/
structure Cor312ToABCBridgeInterfaceV2 where
  carrier : Type u
  hullData : IQHullLogVolumeInterface carrier
  epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
    Cor312EpsilonArithmeticComparisonV2 hullData epsilon

theorem cor312ToABCBridge_heightBoundV2 (D : Cor312ToABCBridgeInterfaceV2) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real,
      ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A := by
  refine heightWeightBound_of_normalizedVolumeComparison
    (P := IsABCTriple)
    (height := fun a b c => Height.logHeight₁ (abcRationalPoint a c))
    (weight := fun a b c => arithmeticWeight (abcRationalPoint a c))
    (volume := fun delta hdelta a b c =>
      (D.hullData.logVolume
        ((D.epsilonComparison delta hdelta).comparisonRegion a b c)).toReal)
    (thetaBound := (D.hullData.logVolume D.hullData.hull).toReal)
    (hweight_nonneg := fun a b c _ => arithmeticWeight_nonneg _)
    (hcomparison := fun delta hdelta =>
      ⟨(D.epsilonComparison delta hdelta).height_le_comparisonRegionVolume,
        (D.epsilonComparison delta hdelta).regionVolume_le_normalizedWeight⟩)

#check Cor312EpsilonArithmeticComparisonV2
#check Cor312ToABCBridgeInterfaceV2
#check cor312ToABCBridge_heightBoundV2
#print axioms cor312ToABCBridge_heightBoundV2


theorem cor312ToABCBridge_abcConjectureV2
    (D : Cor312ToABCBridgeInterfaceV2) : ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mpr
    (cor312ToABCBridge_heightBoundV2 D)

#check cor312ToABCBridge_abcConjectureV2
#print axioms cor312ToABCBridge_abcConjectureV2

end LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual