import tmp.sheaf.n8.closure.C1ValueGroupActualAttempt
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# C1UnitQuotientValueGroupAttempt: finite unit quotient ≃ value group

Uses `finiteUnitToValueGroup_ker` (kernel = integral units) and the actual
surjectivity of `finitePlaceLocalValue` to construct

  ((v.adicCompletion F)ˣ ⧸ (v.adicCompletionIntegers F).units) ≃* Multiplicative ℤ.

This is the actual finite-place quotient comparison.  It does not produce an
isomorphism `(units) ≃* valueGroup`; the quotient by integral units is a
strictly larger side.  The infinite-place quotient/equivalence is not
constructed and is the named obligation below.  No arbitrary equivalence.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1UnitQuotientValueGroupAttempt

universe u

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open IsDedekindDomain
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

/-- Actual finite-place quotient equivalence: units modulo the integral-unit
kernel is the value group. -/
noncomputable def finiteUnitQuotientEquivValueGroup
    (v : HeightOneSpectrum (𝓞 F)) :
    ((v.adicCompletion F)ˣ ⧸ (v.adicCompletionIntegers F).units) ≃*
      finitePlaceValueGroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (finiteUnitToValueGroup_ker (F := F) v)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (finiteUnitToValueGroup (F := F) v)
      (finitePlacePrimeStripValueMap_surjective (F := F) v))

/-- Exact missing infinite-place quotient comparison. -/
def InfiniteUnitQuotientEquivExists
    (w : NumberField.InfinitePlace F) : Prop :=
  Nonempty (((w.Completion)ˣ ⧸
      (infiniteUnitToValueGroup (F := F) w).ker) ≃*
    archimedeanValueGroup)

end LeanFormal.IUT.N8Closure.C1UnitQuotientValueGroupAttempt