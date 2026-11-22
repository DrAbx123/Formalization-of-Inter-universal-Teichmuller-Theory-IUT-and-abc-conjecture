/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1S1902IQHullInterfaceCanonicalActual

/-! # A625 hull: triple-dependent comparison-region alignment evidence

Read-only evidence for the mainline triple-dependent paper region
(`Mzk1PaperComparisonRegionScalingActual`); the canonical files are not changed.

The fixed-identity `scaleShift` of the actual hull cannot support the paper's
height comparison (A618: e.g. the triple `3 + 125 = 128`), so the comparison
region must use the triple-dependent scaling `tripleScale a b c`.  This file
records the alignment facts:

* `tripleScale T 0 0 0 = id`, hence the `(0,0,0)` paper region is the *unscaled*
  `unitRegion ∪ {point 0 0 0}` (the minimal stable fixed-scale shape);
* `paperComparisonRegion_shape` (re-export): the region is exactly
  `tripleScale a b c '' (unitRegion ∪ {point a b c})`;
* the actual S1902 interface's comparison region (with `scaleShift = id`) equals
  the unscaled shape `s1902UnitRegion ∪ {point}`.

No object changed; no sorry/axiom; ABC gate NOT passed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S1902TripleRegionAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual
open LeanFormal.IUT.XiFPaper.Mzk1S1902IQHullInterfaceCanonicalActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- At the zero triple the triple-dependent scaling is the identity. -/
theorem tripleScale_zero : tripleScale T 0 0 0 = id := by
  funext x v
  simp [tripleScale]

/-- The zero-triple paper region is the minimal (unscaled) comparison shape. -/
theorem paperComparisonRegion_zero
    (point : Nat → Nat → Nat → S1902Carrier T) :
    paperComparisonRegion T point 0 0 0 =
      s1902UnitRegion T ∪ ({point 0 0 0} : Set (S1902Carrier T)) := by
  rw [paperComparisonRegion, tripleScale_zero, Set.image_id]

/-- Re-export of the paper-shape identity for the triple-dependent region. -/
theorem tripleRegion_shape
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    paperComparisonRegion T point a b c =
      tripleScale T a b c '' (s1902UnitRegion T ∪ {point a b c}) :=
  paperComparisonRegion_shape T point a b c

/-- Every scaled point of the region is a natural multiple of an unscaled carrier
point (direct unfolding of `tripleScale`). -/
theorem tripleScale_apply
    (a b c : Nat) (x : S1902Carrier T) :
    tripleScale T a b c x =
      fun v => (a + b + c + 1) • x v :=
  rfl

/-- The actual S1902 interface comparison region is unscaled (its `scaleShift` is the
identity), the minimal stable fixed-scale shape. -/
theorem actualComparisonRegion_eq_unscaled
    (point : Nat → Nat → Nat → S1902Carrier T) (a b c : Nat) :
    normalizedComparisonRegion (s1902IQHullInterfaceCanonical T) point a b c =
      s1902UnitRegion T ∪ ({point a b c} : Set (S1902Carrier T)) := by
  simp [normalizedComparisonRegion, s1902IQHullInterfaceCanonical,
    s1902IQHullLogVolumeInterface, s1902ScaleShift]

def tripleRegionRows : List (String × String × String) :=
  [ ("minimal fixed-scale region (zero triple)", "paperComparisonRegion_zero", "PROVED"),
    ("triple-dependent paper shape", "tripleRegion_shape", "PROVED (re-export)"),
    ("scaling unfolding", "tripleScale_apply", "PROVED (rfl)"),
    ("actual interface fixed-scale region", "actualComparisonRegion_eq_unscaled", "PROVED"),
    ("scope", "alignment evidence only; mainline owns scaling file", "INTEGRITY") ]

theorem tripleRegionRows_length : tripleRegionRows.length = 5 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902TripleRegionAlignmentActual.paperComparisonRegion_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902TripleRegionAlignmentActual.tripleRegion_shape
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S1902TripleRegionAlignmentActual.actualComparisonRegion_eq_unscaled

end LeanFormal.IUT.XiFPaper.Mzk1S1902TripleRegionAlignmentActual

end