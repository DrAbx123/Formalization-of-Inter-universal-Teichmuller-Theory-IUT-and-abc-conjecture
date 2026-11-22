import tmp.sheaf.n8.closure.C1P6RamificationTransport

/-!
# C1P6RamificationTransportCondition

Exact valuation/range conditions around `C1P6RamificationTransport`.

- `C1P6RangeCondition` is exact: the top q unit lies in the range of the
  actual completion map; it is equivalent to the transport target by
  definition plus choice of the range witness.
- `C1P6ValuationDivisibility` is the valuation necessary condition: some base
  unit has valuation whose `e`-th power is the top q valuation.  Transport
  implies it via `valuation_completionMap`.
- Valuation divisibility alone is NOT sufficient: the range also requires the
  residue/coefficient class to lie in the image of the completion embedding.
  No production residue-image condition is currently exposed, so no converse
  is claimed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6RamificationTransportCondition

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Exact range condition: the top q unit is in the image of the actual
completion map. -/
def C1P6RangeCondition : Prop :=
  (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X)) ∈
    Set.range (fun u : (NumberFieldFinitePlace.Completion (basePlace X))ˣ =>
      NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.Fmod) (topPlace X)
        (u : NumberFieldFinitePlace.Completion (basePlace X)))

/-- The transport target is exactly the range condition. -/
theorem c1P6RamificationTransport_iff_range :
    C1P6RamificationTransport X ↔ C1P6RangeCondition X := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Exact valuation necessary condition: some base unit has valuation whose
ramification-index power is the top q valuation. -/
def C1P6ValuationDivisibility : Prop :=
  ∃ u : (NumberFieldFinitePlace.Completion (basePlace X))ˣ,
    Valued.v (u : NumberFieldFinitePlace.Completion (basePlace X)) ^
        (basePlace X).maximalIdeal.asIdeal.ramificationIdx'
          (topPlace X).maximalIdeal.asIdeal =
      Valued.v (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X))

/-- Transport implies the exact valuation divisibility condition. -/
theorem c1P6RamificationTransport_imp_valuationDivisibility
    (h : C1P6RamificationTransport X) :
    C1P6ValuationDivisibility X := by
  rcases h with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  rw [← hu]
  exact completionMap_valuation_relation (X := X) u

end LeanFormal.IUT.N8Closure.C1P6RamificationTransportCondition