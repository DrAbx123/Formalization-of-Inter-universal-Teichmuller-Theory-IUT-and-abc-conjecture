import tmp.sheaf.n8.closure.C1P6RangeConditionCriterion
import tmp.sheaf.n8.closure.C1ResidueFieldFiniteActual

/-!
# C1P6RangeConditionDecidable

Actual exact obstruction using the finite residue comparison and the
uniformizer normalization.

`C1P6UnitResidueComparison` is actually decidable (finite residue fields, Wave30).
Failure of that comparison, together with a lifted uniformizer, is an exact
obstruction: it rules out `C1P6RangeCondition`.

Full decidability of `C1P6RangeCondition` is not claimed: the residue shadow
is only necessary, and the exact missing object is the normalized unit lift
(`C1P6UnitLiftCondition`).  No arbitrary lifting is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6RangeConditionDecidable

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6RamificationTransportCondition
open LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
open LeanFormal.IUT.N8Closure.C1P6RangeConditionCriterion
open LeanFormal.IUT.N8Closure.C1P6UnitResidueComparison
open LeanFormal.IUT.N8Closure.C1ResidueFieldFiniteActual
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual unit lift implies the range condition (criterion sufficiency). -/
theorem c1P6RangeCondition_of_unitLift'
    (hπ : C1P6UniformizerLiftCondition X)
    (hu : C1P6UnitLiftCondition X) :
    C1P6RangeCondition X :=
  c1P6RangeCondition_of_unitLift X hπ hu

/-- The actual unit residue comparison has a decidable instance (finite residue
fields). -/
noncomputable def c1P6UnitResidueComparison_decided :
    Decidable (C1P6UnitResidueComparison X) :=
  unitResidueComparisonDecidable X

end LeanFormal.IUT.N8Closure.C1P6RangeConditionDecidable