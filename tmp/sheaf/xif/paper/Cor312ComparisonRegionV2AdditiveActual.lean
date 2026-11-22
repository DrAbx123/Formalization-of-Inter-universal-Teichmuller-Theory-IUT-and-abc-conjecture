import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
noncomputable section
open LeanFormal.IUT
universe u
namespace LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2AdditiveActual

/-- Additive V2 per-epsilon data: explicit point-dependent region and volume,
with the height comparison carrying the global additive constant A. -/
structure Cor312EpsilonArithmeticComparisonAdditiveV2 {X : Type u}
    (W : IQHullLogVolumeInterface X) (epsilon A : Real) where
  comparisonRegion : Nat → Nat → Nat → Set X
  logShellPoint : Nat → Nat → Nat → X
  logShellPoint_mem :
    ∀ a b c : Nat, logShellPoint a b c ∈ comparisonRegion a b c
  height_le_comparisonRegionVolume_add :
    ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * (W.logVolume (comparisonRegion a b c)).toReal + A
  regionVolume_le_normalizedWeight :
    ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
      (W.logVolume (comparisonRegion a b c)).toReal ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
          (W.logVolume W.hull).toReal + D

/-- Additive V2 bridge interface. -/
structure Cor312ToABCBridgeInterfaceV2Additive where
  carrier : Type u
  hullData : IQHullLogVolumeInterface carrier
  Aeps : Real → Real
  epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
    Cor312EpsilonArithmeticComparisonAdditiveV2 hullData epsilon (Aeps epsilon)

theorem abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditiveV2
    (D : Cor312ToABCBridgeInterfaceV2Additive) :
    ABCHeightWeightAdditiveBoundV2 := by
  refine heightWeightBound_of_normalizedVolumeComparison
    (P := IsABCTriple)
    (height := fun a b c => Height.logHeight₁ (abcRationalPoint a c))
    (weight := fun a b c => arithmeticWeight (abcRationalPoint a c))
    (volume := fun delta hdelta a b c =>
      (D.hullData.logVolume
          ((D.epsilonComparison delta hdelta).comparisonRegion a b c)).toReal +
        D.Aeps delta / (1 + delta))
    (thetaBound := (D.hullData.logVolume D.hullData.hull).toReal)
    (hweight_nonneg := fun a b c _ => arithmeticWeight_nonneg _)
    (hcomparison := fun delta hdelta =>
      ⟨by
        intro a b c habc
        have h := (D.epsilonComparison delta hdelta).height_le_comparisonRegionVolume_add
          a b c habc
        have hden : (1 + delta) ≠ 0 := by linarith
        calc
          Height.logHeight₁ (abcRationalPoint a c)
              ≤ (1 + delta) *
                  (D.hullData.logVolume
                    ((D.epsilonComparison delta hdelta).comparisonRegion a b c)).toReal +
                  D.Aeps delta := h
          _ = (1 + delta) *
                ((D.hullData.logVolume
                    ((D.epsilonComparison delta hdelta).comparisonRegion a b c)).toReal +
                  D.Aeps delta / (1 + delta)) := by
                field_simp [hden]
      , by
        obtain ⟨D0, hvol⟩ :=
          (D.epsilonComparison delta hdelta).regionVolume_le_normalizedWeight
        refine ⟨D0 + D.Aeps delta / (1 + delta), ?_⟩
        intro a b c habc
        have h := hvol a b c habc
        have hden : (1 + delta) ≠ 0 := by linarith
        calc
          (D.hullData.logVolume
              ((D.epsilonComparison delta hdelta).comparisonRegion a b c)).toReal +
              D.Aeps delta / (1 + delta)
              ≤ (1 + delta) * arithmeticWeight (abcRationalPoint a c) +
                  (D.hullData.logVolume D.hullData.hull).toReal + D0 +
                  D.Aeps delta / (1 + delta) := by linarith
          _ = (1 + delta) * arithmeticWeight (abcRationalPoint a c) +
                (D.hullData.logVolume D.hullData.hull).toReal +
                (D0 + D.Aeps delta / (1 + delta)) := by ring
      ⟩)

theorem abcConjecture_of_additiveV2
    (D : Cor312ToABCBridgeInterfaceV2Additive) : ABCConjecture :=
  abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mpr
    (abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditiveV2 D)

#check Cor312EpsilonArithmeticComparisonAdditiveV2
#check Cor312ToABCBridgeInterfaceV2Additive
#check abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditiveV2
#check abcConjecture_of_additiveV2
#print axioms abcConjecture_of_additiveV2

end LeanFormal.IUT.XiFPaper.Cor312ComparisonRegionV2AdditiveActual