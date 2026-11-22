import tmp.sheaf.n8.closure.C1UnitQuotientValueGroupAttempt
import tmp.sheaf.n8.closure.C1ValueGroupActualAttempt
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# C1InfiniteUnitQuotientAttempt: infinite-place unit quotient

`infinitePlaceCompletionDegree` is an actual monoid hom
`(w.Completion)ˣ →* archimedeanValueGroup`; its kernel is the norm-one units.
Conditionally on its surjectivity, the quotient by that kernel is the
archimedean value group.  No production surjectivity theorem is present, so
surjectivity is the exact named obligation.  No arbitrary equivalence.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1InfiniteUnitQuotientAttempt

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.C1UnitQuotientValueGroupAttempt
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

/-- Actual conditional quotient equivalence: if the infinite degree map is
surjective, quotienting by its kernel gives the archimedean value group. -/
noncomputable def infiniteUnitQuotientEquivOfSurjective
    (w : NumberField.InfinitePlace F)
    (h : Function.Surjective (infiniteUnitToValueGroup (F := F) w)) :
    ((w.Completion)ˣ ⧸ (infiniteUnitToValueGroup (F := F) w).ker) ≃*
      archimedeanValueGroup :=
  QuotientGroup.quotientKerEquivOfSurjective _ h

/-- Exact missing production statement: surjectivity of the infinite degree
map.  Sole named sorry. -/
theorem infiniteUnitDegree_surjective_attempt
    (w : NumberField.InfinitePlace F) :
    Function.Surjective (infiniteUnitToValueGroup (F := F) w) := by
  sorry

/-- The named target `InfiniteUnitQuotientEquivExists w`, assembled from the
actual conditional quotient and the surjectivity obligation. -/
theorem infiniteUnitQuotientEquiv_actual
    (w : NumberField.InfinitePlace F) :
    InfiniteUnitQuotientEquivExists (F := F) w :=
  ⟨infiniteUnitQuotientEquivOfSurjective (F := F) w
    (infiniteUnitDegree_surjective_attempt (F := F) w)⟩

end LeanFormal.IUT.N8Closure.C1InfiniteUnitQuotientAttempt