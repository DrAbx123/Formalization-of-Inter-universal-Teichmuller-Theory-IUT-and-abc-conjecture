import tmp.sheaf.n8.closure.C1InfiniteDegreeSurjectiveAttempt
import tmp.sheaf.n8.closure.C1UnitQuotientValueGroupAttempt

/-!
# C1PlaceValueGroupActual: finite/infinite unit quotients = value groups

Assembles the actual quotient equivalences:
- finite: `(units) ⧸ integralUnits ≃* Multiplicative ℤ`;
- infinite: `(units) ⧸ normOne ≃* Multiplicative ℝ` (from the proved infinite
  surjectivity and quotient-kernel theorem).

The full-unit `C1FiberMonEquivData` is a *different* target: it asks for
`(units) ≃* valueGroup`, not the quotient.  The quotient assembly does not
provide that; the exact full-unit target remains the named sorry.  No
arbitrary equivalence is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual

universe u v

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.C1ValueGroupActualAttempt
open LeanFormal.IUT.N8Closure.C1UnitQuotientValueGroupAttempt
open LeanFormal.IUT.N8Closure.C1InfiniteUnitQuotientAttempt
open LeanFormal.IUT.N8Closure.C1InfiniteDegreeSurjectiveAttempt
open LeanFormal.IUT.N8Closure.C1FiberMonEquivAttempt
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open IsDedekindDomain
open scoped NumberField

variable {F : Type u} [Field F] [NumberField F]

instance placeUnitMonoidGroup (P : NumberFieldPlaceIndex (F := F)) :
    Group (PlaceUnitMonoid (F := F) P) := by
  cases P <;> infer_instance

/-- Kernel of the actual unit -> value group comparison at a place. -/
noncomputable def placeUnitKernel
    (P : NumberFieldPlaceIndex (F := F)) :
    Subgroup (PlaceUnitMonoid (F := F) P) :=
  match P with
  | Sum.inl v => (v.adicCompletionIntegers F).units
  | Sum.inr w => (infiniteUnitToValueGroup (F := F) w).ker

instance placeUnitKernel_normal (P : NumberFieldPlaceIndex (F := F)) :
    (placeUnitKernel (F := F) P).Normal := by
  cases P <;> infer_instance

/-- Actual finite/infinite quotient equivalence. -/
noncomputable def placeUnitQuotientEquivValueGroup
    (P : NumberFieldPlaceIndex (F := F)) :
    (PlaceUnitMonoid (F := F) P ⧸ placeUnitKernel (F := F) P) ≃*
      SourcePlaceValueGroup (F := F) P :=
  match P with
  | Sum.inl v => finiteUnitQuotientEquivValueGroup (F := F) v
  | Sum.inr w => Classical.choice (infiniteUnitQuotientEquiv_actual_closed (F := F) w)

end LeanFormal.IUT.N8Closure.C1PlaceValueGroupActual