import tmp.sheaf.xif.paper.Cor312ComparisonRegionV2Actual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

/-! # Triple-dependent scaling interface (design) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TripleDependentScalingInterfaceShaActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2Actual

universe u

/-- Interface where the comparison region and the scaling/shell point depend on the
ABC triple `(a,b,c)`, not only on `epsilon`. -/
structure TripleDependentScalingInterface (X : Type u) where
  hullData : IQHullLogVolumeInterface X
  comparisonRegion : Nat → Nat → Nat → Set X
  scalingPoint : Nat → Nat → Nat → X
  scalingPoint_mem : forall a b c : Nat, scalingPoint a b c ∈ comparisonRegion a b c
  height_bound : forall (epsilon : Real), 0 < epsilon →
    forall a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (hullData.logVolume (comparisonRegion a b c)).toReal
  volume_bound : forall (epsilon : Real), 0 < epsilon → exists D : Real,
    forall a b c : Nat, IsABCTriple a b c →
      (hullData.logVolume (comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (hullData.logVolume hullData.hull).toReal + D


/-- Canonical paper region shape: `region a b c = tripleScale a b c '' (unitRegion ∪ {pt a b c})`. -/
noncomputable def ofTripleScale {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (tripleScale : Nat → Nat → Nat → X → X)
    (pt : Nat → Nat → Nat → X)
    (height_bound : forall (epsilon : Real), 0 < epsilon →
      forall a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (W.logVolume
            (tripleScale a b c '' (W.unitRegion ∪ {pt a b c}))).toReal)
    (volume_bound : forall (epsilon : Real), 0 < epsilon → exists D : Real,
      forall a b c : Nat, IsABCTriple a b c →
        (W.logVolume (tripleScale a b c '' (W.unitRegion ∪ {pt a b c}))).toReal ≤
          (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D) :
    TripleDependentScalingInterface X where
  hullData := W
  comparisonRegion := fun a b c => tripleScale a b c '' (W.unitRegion ∪ {pt a b c})
  scalingPoint := fun a b c => tripleScale a b c (pt a b c)
  scalingPoint_mem := by
    intro a b c
    exact Set.mem_image_of_mem (tripleScale a b c)
      (Set.mem_union_right _ (Set.mem_singleton (pt a b c)))
  height_bound := height_bound
  volume_bound := volume_bound

namespace TripleDependentScalingInterface

variable {X : Type u} (D : TripleDependentScalingInterface X)

/-- Forget the triple dependence to the V2 epsilon comparison data. -/
noncomputable def toComparisonV2 (epsilon : Real) (heps : 0 < epsilon) :
    Cor312EpsilonArithmeticComparisonV2 D.hullData epsilon where
  comparisonRegion := D.comparisonRegion
  logShellPoint := D.scalingPoint
  logShellPoint_mem := D.scalingPoint_mem
  height_le_comparisonRegionVolume := D.height_bound epsilon heps
  regionVolume_le_normalizedWeight := D.volume_bound epsilon heps

/-- Package the triple-dependent interface as a concrete V2 bridge. -/
noncomputable def toBridge : Cor312ToABCBridgeInterfaceV2 where
  carrier := X
  hullData := D.hullData
  epsilonComparison := fun epsilon heps => D.toComparisonV2 epsilon heps

/-- Consumer: the triple-dependent interface gives ABCConjecture. -/
theorem toBridge_abc : ABCConjecture :=
  cor312ToABCBridge_abcConjectureV2
    (TripleDependentScalingInterface.toBridge D)

end TripleDependentScalingInterface

end LeanFormal.IUT.XiFPaper.Mzk1TripleDependentScalingInterfaceShaActual
