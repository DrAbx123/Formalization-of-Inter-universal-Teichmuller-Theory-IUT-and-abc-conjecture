import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual

/-!
# shehdd A625 triple-dependent region alignment (Sha, read-only)

Aligns the shehdd lane with mainline's green canonical triple-dependent region:
re-exports `tripleScale`, `paperComparisonRegion`, their shape equation, the
`TripleDependentComparison` structure and the conditional ABC theorem.  Canonical
file remains mainline-owned; this file only imports it.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1TripleDependentRegionAlignShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Read-only aligned triple-dependent scale. -/
noncomputable def alignedTripleScale (a b c : Nat) :
    S1902Carrier T → S1902Carrier T :=
  tripleScale T a b c

/-- Read-only aligned paper comparison region. -/
noncomputable def alignedRegion
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    Set (S1902Carrier T) :=
  paperComparisonRegion T point a b c

theorem alignedRegion_shape
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    alignedRegion T point a b c =
      alignedTripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c}) :=
  paperComparisonRegion_shape T point a b c

/-- Read-only aligned conditional ABC. -/
theorem aligned_abc
    (point : Nat → Nat → Nat → S1902Carrier T)
    (C : TripleDependentComparison T point) : ABCConjecture :=
  abc_of_tripleComparison T point C

end LeanFormal.IUT.XiFPaper.Mzk1TripleDependentRegionAlignShaActual

/-! ### Axiom gate for the canonical triple-dependent ABC -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual.abc_of_tripleComparison
