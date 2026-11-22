import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # S1402: dependent-place HDD source

The uniform family E : Fin rank -> Type with localEquiv to every 1-column
local field was the exact obstruction in S1356.  Here E is dependent on the
places: for a finite set s of finite places, E v = localField v.  The
dependent field family and its normed-field structure are actual.

The remaining exact first field is the output-dependent allowed-image family
image : Theorem311Output I -> Set ((v : s) -> localField v), together with its
compactness/nonemptiness/coordinate data and the det bookkeeping.  The hull
below is the actual LocalFieldProductHull.hull of that image; no arbitrary
Set, rank-one or Fin1 surrogate is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.LocalFieldProductHull

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

/-- Dependent local-field family over a finite set of rational places. -/
abbrev S1402DependentE (s : Finset (NumberField.FinitePlace ℚ)) :
    {v : NumberField.FinitePlace ℚ // v ∈ s} → Type :=
  fun v => (oneColumnStructure).localField v.1

/-- Actual normed-field structure on the dependent family. -/
noncomputable instance s1402DependentENormedField
    (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    NormedField (S1402DependentE s v) :=
  inferInstance

/-- Exact first field: the output-dependent HDD allowed-image family over the
dependent local-field product.  No inhabitant is supplied. -/
abbrev S1402DependentImageRequired (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) :=
  Theorem311Output I → Set ((v : {v // v ∈ s}) → S1402DependentE s v)

/-- Exact dependent-place HDD source: image data plus the actual hull inputs and
det bookkeeping.  Unlike S1300 there is no uniform localEquiv field: the
dependent field family is already the local field at each place. -/
structure S1402DependentHDDSource (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) where
  image : S1402DependentImageRequired I s
  compact_closure : ∀ o, IsCompact (closure (image o))
  nonempty : ∀ o, (image o).Nonempty
  coordinate_nonzero : ∀ (o) (v : {v // v ∈ s}), ∃ x ∈ image o, x v ≠ 0
  detData : DetTensorPowerLogVolumeBookkeeping
    (Set ((v : {v // v ∈ s}) → S1402DependentE s v))

namespace S1402DependentHDDSource

variable {I : Input Label Choice} {s : Finset (NumberField.FinitePlace ℚ)}

/-- Actual hull of the dependent image, using LocalFieldProductHull.hull. -/
noncomputable def dependentHull (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    Set ((v : {v // v ∈ s}) → S1402DependentE s v) :=
  @LocalFieldProductHull.hull {v // v ∈ s} (S1402DependentE s)
    (s1402DependentENormedField s) (D.image o)

/-- The dependent hull is exactly the actual LocalFieldProductHull.hull of the
image, not an arbitrary set. -/
theorem dependentHull_eq (D : S1402DependentHDDSource I s)
    (o : Theorem311Output I) :
    D.dependentHull o =
      @LocalFieldProductHull.hull {v // v ∈ s} (S1402DependentE s)
        (s1402DependentENormedField s) (D.image o) := rfl

end S1402DependentHDDSource

end LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual

end
