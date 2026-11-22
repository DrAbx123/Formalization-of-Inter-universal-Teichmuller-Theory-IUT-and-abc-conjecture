import tmp.sheaf.n8.closure.C1P6RamificationTransportCondition
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs

/-!
# C1P6RangeConditionSourceAttempt

Source attempt at `C1P6RangeCondition`: the top q unit lies in the unit image
of the completion map.

Decisive residue obstruction: the top q has valuation `< 1`, hence lies in the
maximal ideal of the top completion integers and reduces to `0` in the residue
field.  A residue/coefficient comparison would need a uniformizer
normalization of q (a non-integral-unit reduction); production does not expose
one.  No arbitrary unit, residue map, or compatibility is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6RangeConditionSourceAttempt

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6RamificationTransportCondition
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Top q is in the completion integers (valuation `<1` implies `≤1`). -/
theorem topQUnit_mem_completionIntegers :
    (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X)) ∈
      (topPlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.F := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
    (R := NumberField.RingOfIntegers X.S.arithmetic.F)
    (K := X.S.arithmetic.F) (v := (topPlace X).maximalIdeal)]
  exact le_of_lt (C9QPilotRegion.nativeQ X).valuation_lt_one

/-- Actual residue obstruction: the top q integer element lies in the maximal
ideal, so its residue is `0` and cannot be compared as a unit residue class. -/
theorem topQUnit_in_maximalIdeal :
    (⟨(topQUnit X : NumberFieldFinitePlace.Completion (topPlace X)),
        topQUnit_mem_completionIntegers X⟩ :
      (topPlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.F) ∈
      IsLocalRing.maximalIdeal
        ((topPlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.F) := by
  rw [LeanFormal.IUT.NumberFieldFinitePlace.mem_maximalIdeal_iff_valued_lt_one]
  exact (C9QPilotRegion.nativeQ X).valuation_lt_one

/-- Exact obstruction Prop: top q reduces to the zero class, so a naive unit
residue comparison is undefined. -/
def C1P6ResidueClassObstruction : Prop :=
  (⟨(topQUnit X : NumberFieldFinitePlace.Completion (topPlace X)),
      topQUnit_mem_completionIntegers X⟩ :
    (topPlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.F) ∈
    IsLocalRing.maximalIdeal
      ((topPlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.F)

theorem c1P6ResidueClassObstruction_actual :
    C1P6ResidueClassObstruction X :=
  topQUnit_in_maximalIdeal X

end LeanFormal.IUT.N8Closure.C1P6RangeConditionSourceAttempt