import tmp.sheaf.xif.paper.S1356HDDHullDetSourceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # S1385: true HDD hull+det source, exact first field

Read S1300/S1356, LocalFieldProductHull, and
HullDeterminantLogVolumeFrozenSpec.

Actual donors:
* LocalFieldProductHull.hull / exists_hull_eq_region / integralSpan_eq_hull;
* hullDeterminantLogVolumeFrozenSpec_holds;
* S1300 actual hull/det donor facts.

The S1300 source requires a rank, a finite local-field family E, an
output-dependent image, compactness/nonemptiness/coordinate nondegeneracy,
a uniform ring equivalence of every factor to the 1-column local field at
every finite place, and det bookkeeping.  The hull and det parts are actual
donors; the uniform localEquiv is not constructible from the tree.  This file
records that exact first field and does not use rank-one, Fin 1, or an
arbitrary Set as a lattice.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S1356HDDHullDetSourceActual
open LeanFormal.IUT.LocalFieldProductHull

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-- Exact first field: a uniform family E with a ring equivalence of every
factor to each 1-column local field, for every finite place. -/
abbrev S1385UniformLocalEquiv (rank : Nat) (E : Fin rank → Type)
    [∀ i, NormedField (E i)] : Type :=
  S1356UniformLocalEquiv rank E

/-- Actual frozen hull+det specification donor. -/
theorem s1385FrozenSpec_actual :
    HullDeterminantLogVolumeFrozenSpec :=
  hullDeterminantLogVolumeFrozenSpec_holds

/-- Actual hull equals the integral span on a compact nondegenerate
coordinatewise-nonzero image. -/
theorem s1385ActualIntegralSpan_eq_hull
    {J : Type*} [Finite J] {E : J → Type*} [∀ j, NormedField (E j)]
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    {S : Set ((j : J) → E j)} (hS : IsCompact S) (hne : S.Nonempty)
    (hcoord : ∀ j, ∃ x ∈ S, x j ≠ 0) :
    (Submodule.span (integralRing hna) S : Set ((j : J) → E j)) = hull S :=
  integralSpan_eq_hull hna hS hne hcoord

end LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual

end
