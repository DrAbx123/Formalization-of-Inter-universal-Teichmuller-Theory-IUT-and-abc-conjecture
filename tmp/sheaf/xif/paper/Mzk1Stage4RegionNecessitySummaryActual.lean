import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual
import tmp.sheaf.xif.paper.Mzk1Stage4TripleRegionAlignmentActual

/-! # Mzk1Stage4RegionNecessitySummaryActual (stage4 lane; necessity summary)

A636 module: summary of WHY the triple-dependent comparison region is necessary —
identity scaling gives a fixed region independent of the triple (A618 obstruction),
while the canonical triple scaling makes the region triple-dependent; a concrete model
shows the regions actually differ.  Canonical files only READ.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4RegionNecessitySummaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperRegionIdentityObstructionTInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The necessity summary for the triple-dependent region. -/
structure RegionNecessitySummary (T : SourceNativeInitialThetaData.{0} l) where
  /-- identity scaling gives a triple-INDEPENDENT region. -/
  identity_constant : ∀ (point : S1902Carrier T) (a b c a' b' c' : Nat),
    region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a b c =
      region (identityScaling (S1902Carrier T) (s1902UnitRegion T) point) a' b' c'
  /-- the canonical triple scaling gives the paper region shape. -/
  canonical_shape : ∀ (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat),
    region (canonicalScaling T point) a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c})

/-- Construct the region-necessity summary. -/
noncomputable def regionNecessitySummary : RegionNecessitySummary T where
  identity_constant := fun point a b c a' b' c' =>
    s1902_identity_region_independent T point a b c a' b' c'
  canonical_shape := fun point a b c =>
    canonicalScaling_region_shape T point a b c

/-- The real model: the triple-dependent regions actually DIFFER. -/
theorem realRegions_differ :
    region realScaling 1 1 1 ≠ region realScaling 0 0 0 := by
  intro h
  have hmem : (2 : Real) ∈ region realScaling 1 1 1 := by
    refine ⟨1 / 2, ?_, ?_⟩
    · left
      constructor <;> norm_num [realUnit]
    · norm_num [realScaling, realScale]
  rw [h] at hmem
  rcases hmem with ⟨x, hx, hxeq⟩
  simp only [realScaling, realScale, realPt] at hx hxeq
  rcases hx with hx | hx
  · norm_num at hxeq
    linarith [hx.2]
  · subst hx
    norm_num at hxeq

#check RegionNecessitySummary
#check regionNecessitySummary
#check realRegions_differ

end LeanFormal.IUT.XiFPaper.Mzk1Stage4RegionNecessitySummaryActual
end
