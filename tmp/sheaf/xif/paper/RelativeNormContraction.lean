import tmp.sheaf.xif.paper.RelativeNormCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-!
# Relative norm contraction: conditional proof and exact missing norm formula

The actual relative norm map is constructed in RelativeNormCompletion:

  relativeNormCompletion : Completion (nativeFPlaceOverBad X) ->
    Completion (nativeBadBasePlace X).

For any nonzero upper completion element x, a finite extension of
nonarchimedean local fields satisfies a valuation power law for the algebra norm:

  Valued.v (relativeNormCompletion x) = (Valued.v x) ^ n

for a positive integer n (the relative degree/ramification factor, depending on
the chosen normalization).  From this formula, x with Valued.v x < 1 gives
Valued.v (relativeNormCompletion x) < 1 by pow_lt_one.

What the tree currently has is the norm transport law only for images of
base-field elements:

  norm_completionMap_pow (base x) : norm x ^ relativeCompletionDegree.

It does not contain the general arbitrary-element valuation power law for
Algebra.norm on the finite completion extension.  That is the exact missing
norm formula; no arbitrary formula or inequality is selected below.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.RelativeNormContraction

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The target contraction statement for the actual native q. -/
def NativeQRelativeNormContraction : Prop :=
  (Valued.v (relativeNormCompletion (X := X) (nativeQActual X).q) :
    WithZero (Multiplicative Int)) < 1

/-- The general missing valuation power law for the relative algebra norm. -/
def RelativeNormValuationPower (n : Nat) : Prop :=
  0 < n ∧ forall (x : NativeFCompletion (X := X)), x ≠ 0 ->
    Valued.v (relativeNormCompletion (X := X) x) =
      (Valued.v x) ^ n

/-- The exact missing norm formula, existential form. -/
def MissingRelativeNormValuationFormula : Prop :=
  exists n : Nat, RelativeNormValuationPower (X := X) n

/-- Conditional contraction from the exact norm valuation power law. -/
theorem nativeQRelativeNormContraction_of_power
    (n : Nat) (h : RelativeNormValuationPower (X := X) n) :
    NativeQRelativeNormContraction (X := X) := by
  rcases h with ⟨hnpos, hformula⟩
  unfold NativeQRelativeNormContraction
  rw [hformula (nativeQActual X).q (nativeQActual X).q_ne_zero]
  exact pow_lt_one₀ bot_le (nativeQActual X).valuation_lt_one hnpos

/-- Conditional contraction from the existential missing formula. -/
theorem nativeQRelativeNormContraction_of_missingFormula
    (h : MissingRelativeNormValuationFormula (X := X)) :
    NativeQRelativeNormContraction (X := X) := by
  rcases h with ⟨n, hpow⟩
  exact nativeQRelativeNormContraction_of_power (X := X) n hpow

/-- The nonzero part of the relative norm q-candidate law, also conditional on
the power formula because the norm of a nonzero element is nonzero. -/
theorem nativeQRelativeNorm_ne_zero_of_power
    (n : Nat) (h : RelativeNormValuationPower (X := X) n) :
    relativeNormCompletion (X := X) (nativeQActual X).q ≠ 0 := by
  rcases h with ⟨hnpos, hformula⟩
  rw [hformula (nativeQActual X).q (nativeQActual X).q_ne_zero]
  exact pow_ne_zero n
    (FinitePlaceQCandidate.valuation_ne_zero (nativeQActual X))

/-- The exact missing general theorem: for the finite completion extension, the
algebra norm has a positive valuation power law on every nonzero element. -/
def MissingAlgebraNormValuationPowerTheorem : Prop :=
  exists n : Nat, 0 < n ∧
    forall (x : NativeFCompletion (X := X)), x ≠ 0 ->
      Valued.v (relativeNormCompletion (X := X) x) =
        (Valued.v x) ^ n

/-- The missing theorem is exactly the formula needed by the contraction
consumer. -/
theorem missingAlgebraNormValuationPowerTheorem_iff :
    MissingAlgebraNormValuationPowerTheorem (X := X) ↔
      MissingRelativeNormValuationFormula (X := X) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.RelativeNormContraction

end