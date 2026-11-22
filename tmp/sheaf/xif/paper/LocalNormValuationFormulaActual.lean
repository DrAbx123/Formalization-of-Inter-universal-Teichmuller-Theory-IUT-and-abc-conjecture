import tmp.sheaf.xif.paper.RelativeNormCompletion
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Local norm valuation formula on the completion extension

The actual relative norm is Algebra.norm over the completion algebra

  nativeBaseCompletionRaw -> nativeFCompletion.

The desired local norm valuation formula is

  Valued.v (Algebra.norm base x) = (Valued.v x) ^ finrank

for the static valuations on the two completions.  Mathlib provides the field
norm, its zero criterion, and norm of base elements, but no general
norm-valuation formula for the actual completion extension.

This file records the formula as the exact missing theorem, and the unconditional
base-element special case that follows from Algebra.norm_algebraMap.  No arbitrary
formula/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.LocalNormValuationFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual relative norm on the completion extension. -/
abbrev localNorm : NativeFCompletion (X := X) → NativeBaseCompletionRaw (X := X) :=
  relativeNormRaw (X := X)

/-- The exact local norm valuation formula for the actual completion extension.
This is the missing theorem; it is not assumed as a global axiom. -/
def LocalNormValuationFormula : Prop :=
  ∀ x : NativeFCompletion (X := X),
    (Valued.v (localNorm (X := X) x) : WithZero (Multiplicative Int)) =
      (Valued.v x : WithZero (Multiplicative Int)) ^
        Module.finrank (NativeBaseCompletionRaw (X := X))
          (NativeFCompletion (X := X))

/-- The base-element special case is actual Mathlib: Algebra.norm_algebraMap
is the finrank power. -/
theorem localNorm_algebraMap (a : NativeBaseCompletionRaw (X := X)) :
    localNorm (X := X) (algebraMap (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) a) =
      a ^ Module.finrank (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) := by
  unfold localNorm relativeNormRaw
  letI := relativeCompletionAlgebra (X := X)
  haveI : Module.Free (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) := inferInstance
  exact Algebra.norm_algebraMap a

/-- Base-element valuation specialization of the missing formula: if the
valuation is multiplicative, the base case is the power of the base valuation.
This is a conditional consequence, not the missing general theorem. -/
theorem localNormValuationFormula_algebraMap
    (hval : ∀ a : NativeBaseCompletionRaw (X := X),
      (Valued.v (algebraMap (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) a) : WithZero (Multiplicative Int)) =
        (Valued.v a : WithZero (Multiplicative Int))) :
    ∀ a : NativeBaseCompletionRaw (X := X),
      (Valued.v (localNorm (X := X) (algebraMap
        (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)) a)) :
        WithZero (Multiplicative Int)) =
        (Valued.v a : WithZero (Multiplicative Int)) ^
          Module.finrank (NativeBaseCompletionRaw (X := X))
            (NativeFCompletion (X := X)) := by
  intro a
  rw [localNorm_algebraMap (X := X) a, map_pow, hval a]

/-! ## Exact missing theorem

Required general formula:

  for every x : Completion (nativeFPlaceOverBad X),
    Valued.v (relativeNormRaw x) =
      (Valued.v x) ^ [Completion F : Completion Fmod].

What is available:
1. Algebra.norm and its zero criterion;
2. Algebra.norm_algebraMap for base elements;
3. Module.Finite of the completion algebra;
4. the base-element valuation specialization under multiplicativity.

What is missing: the general norm-valuation formula on the completion extension
for arbitrary upper elements.  No arbitrary formula or axiom is inserted. -/

end LeanFormal.IUT.XiFPaper.LocalNormValuationFormulaActual

end
