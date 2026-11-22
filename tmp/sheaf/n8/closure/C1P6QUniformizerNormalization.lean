import tmp.sheaf.n8.closure.C1P6RangeConditionSourceAttempt
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# C1P6QUniformizerNormalization

Actual uniformizer normalization of the top q: choose an irreducible uniformizer
`ϖ` in the completion integers, write the integral q element as `u * ϖ^n` using
the actual `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`, and record the
resulting unit/exponent.  No arbitrary uniformizer is assumed: it is chosen
from the actual DVR existence theorem.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.C1P6RamificationTransport
open LeanFormal.IUT.N8Closure.C1P6RangeConditionSourceAttempt
open LeanFormal.IUT.NumberFieldFinitePlace
open IsDedekindDomain
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

abbrev TopIntegers (X : N8NativeInput l) : Type :=
  (topPlace X).maximalIdeal.adicCompletionIntegers X.S.arithmetic.F

/-- The integral q element. -/
noncomputable def qInteger : TopIntegers X :=
  ⟨topQUnit X, topQUnit_mem_completionIntegers X⟩

theorem qInteger_ne_zero : qInteger X ≠ 0 := by
  intro h
  have hq : (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X)) = 0 := by
    simpa [qInteger] using congrArg (fun y : TopIntegers X =>
      (y : NumberFieldFinitePlace.Completion (topPlace X))) h
  exact Units.ne_zero (topQUnit X) hq

/-- A chosen actual irreducible uniformizer in the completion integers. -/
noncomputable def chosenUniformizer : TopIntegers X :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible (TopIntegers X))

theorem chosenUniformizer_irreducible : Irreducible (chosenUniformizer X) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (TopIntegers X))

/-- Actual q = uniformizer^n * unit normalization. -/
structure C1P6QUniformizerNormalization (X : N8NativeInput l) where
  uniformizer : TopIntegers X
  irreducible : Irreducible uniformizer
  exponent : ℕ
  unit : (TopIntegers X)ˣ
  q_eq : (topQUnit X : NumberFieldFinitePlace.Completion (topPlace X)) =
    (unit : NumberFieldFinitePlace.Completion (topPlace X)) *
      (uniformizer : NumberFieldFinitePlace.Completion (topPlace X)) ^ exponent

/-- Actual normalization from the DVR factorization. -/
noncomputable def c1P6QUniformizerNormalization :
    C1P6QUniformizerNormalization X :=
  let π := chosenUniformizer X
  let hπ := chosenUniformizer_irreducible X
  let hex := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (x := qInteger X) (qInteger_ne_zero X) hπ
  { uniformizer := π
    irreducible := hπ
    exponent := Classical.choose hex
    unit := Classical.choose (Classical.choose_spec hex)
    q_eq := by
      have hcast := congrArg (fun y : TopIntegers X =>
        (y : NumberFieldFinitePlace.Completion (topPlace X)))
        (Classical.choose_spec (Classical.choose_spec hex))
      push_cast at hcast
      simpa only [qInteger] using hcast }

end LeanFormal.IUT.N8Closure.C1P6QUniformizerNormalization
