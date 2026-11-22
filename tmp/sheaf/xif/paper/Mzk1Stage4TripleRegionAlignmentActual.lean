import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1Stage4PaperComparisonRegionScalingDesignActual

/-! # Mzk1Stage4TripleRegionAlignmentActual (stage4 lane; alignment, supplemental)

A625 module (stage4 alignment evidence; canonical file
Mzk1PaperComparisonRegionScalingActual is MAINLINE-exclusive and is only READ):
the canonical triple-dependent paper comparison region is an instance of the stage4
generic `PaperComparisonRegionScaling` interface.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4PaperComparisonRegionScalingDesignActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The canonical triple-dependent region as an instance of the generic interface. -/
noncomputable def canonicalScaling (point : Nat → Nat → Nat → S1902Carrier T) :
    PaperComparisonRegionScaling (S1902Carrier T) where
  scale := tripleScale T
  unitRegion := s1902UnitRegion T
  pt := point

/-- The generic interface's region is the canonical paper comparison region. -/
theorem canonicalScaling_region_eq (point : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) :
    region (canonicalScaling T point) a b c = paperComparisonRegion T point a b c :=
  rfl

/-- The canonical region shape restated through the generic interface. -/
theorem canonicalScaling_region_shape (point : Nat → Nat → Nat → S1902Carrier T)
    (a b c : Nat) :
    region (canonicalScaling T point) a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c}) :=
  rfl

#check canonicalScaling
#check canonicalScaling_region_eq
#check canonicalScaling_region_shape

end LeanFormal.IUT.XiFPaper.Mzk1Stage4TripleRegionAlignmentActual
end
