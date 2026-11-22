import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.C9QPilotRegion
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

/-!
# C1P6RamificationTransport

Exact tower transport target from the C1 base Fmod-place to the P6 top
F-place q unit.  The actual completion map and ramification relation exist;
what is missing is a base completion unit mapping to the top q unit.

`completionMap (k := Fmod) w` is the production extension map from the
completion at `comap w` to the completion at `w`.  The target asks for a base
unit whose image is the native q unit.  Ramification is the actual
`valuation_completionMap` relation, but it does not produce such a unit.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6RamificationTransport

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual top F-place of P6 Chain A. -/
abbrev topPlace := nativeFPlaceOverBad X

/-- Actual base Fmod-place below it. -/
abbrev basePlace := NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod) (topPlace X)

/-- Actual top q unit. -/
noncomputable def topQUnit : (NumberFieldFinitePlace.Completion (topPlace X))ˣ :=
  Units.mk0 (C9QPilotRegion.nativeQ X).q (C9QPilotRegion.nativeQ X).q_ne_zero

/-- Exact tower transport target: a base completion unit mapping to the top q
unit under the actual completion map. -/
def C1P6RamificationTransport : Prop :=
  ∃ u : (NumberFieldFinitePlace.Completion (basePlace X))ˣ,
    NumberFieldFinitePlace.completionMap (k := X.S.arithmetic.Fmod) (topPlace X)
      (u : NumberFieldFinitePlace.Completion (basePlace X)) =
      (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X))

/-- Actual ramification relation for the completion map (production donor). -/
theorem completionMap_valuation_relation
    (u : NumberFieldFinitePlace.Completion (basePlace X)) :
    Valued.v u ^
        (basePlace X).maximalIdeal.asIdeal.ramificationIdx'
          (topPlace X).maximalIdeal.asIdeal =
      Valued.v (NumberFieldFinitePlace.completionMap
        (k := X.S.arithmetic.Fmod) (topPlace X) u) :=
  NumberFieldFinitePlace.valuation_completionMap (k := X.S.arithmetic.Fmod) (topPlace X) u

end LeanFormal.IUT.N8Closure.C1P6RamificationTransport