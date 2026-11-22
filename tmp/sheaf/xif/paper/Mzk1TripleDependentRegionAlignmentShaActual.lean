import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1TripleDependentScalingInterfaceShaActual

/-! # Triple-dependent region alignment (canonical paper scaling vs interface) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1TripleDependentRegionAlignmentShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1TripleDependentScalingInterfaceShaActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Canonical paper region has exactly the interface shape. -/
theorem paperRegion_eq_interfaceShape
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    paperComparisonRegion T point a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c}) :=
  paperComparisonRegion_shape T point a b c

/-- The canonical triple-dependent comparison data maps to our interface design. -/
noncomputable def interfaceOfCanonical
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) :
    TripleDependentScalingInterface (S1902Carrier T) :=
  TripleDependentScalingInterface.ofTripleScale (s1902IQHullLogVolumeInterface T)
    (tripleScale T) point
    (by
      intro epsilon heps a b c habc
      simpa [paperComparisonRegion, s1902IQHullLogVolumeInterface] using
        C.height_le_regionVolume epsilon heps a b c habc)
    (by
      intro epsilon heps
      obtain ⟨D, hD⟩ := C.regionVolume_le_weight epsilon heps
      refine ⟨D, ?_⟩
      intro a b c habc
      simpa [paperComparisonRegion, s1902IQHullLogVolumeInterface] using hD a b c habc)

/-- Alignment consumer: canonical ABC through the interface design. -/
theorem canonical_abc_via_interface
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abc_of_tripleComparison T point C

#print axioms canonical_abc_via_interface

end LeanFormal.IUT.XiFPaper.Mzk1TripleDependentRegionAlignmentShaActual
