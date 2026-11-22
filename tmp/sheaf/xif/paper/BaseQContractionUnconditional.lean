import tmp.sheaf.xif.paper.RelativeNormContractionActual
import tmp.sheaf.xif.paper.BaseQUnconditionalActual

/-! # Base q contraction from local norm valuation

The actual base q object is constructed in BaseQUnconditionalActual:

  baseQValue X = relativeNormCompletion (nativeQActual X).q,
  baseQValue_ne_zero.

This file records the local norm valuation formula needed for the contraction

  (Valued.v (baseQValue X) : WithZero (Multiplicative Int)) < 1.

The formula is NOT assumed as an axiom: it is an explicit missing theorem,
together with the positive-degree power monotonicity step.  No arbitrary
bound/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.BaseQContractionUnconditional

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.BaseQUnconditionalActual
open LeanFormal.IUT.XiFPaper.RelativeNormContractionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual base q value from the relative norm. -/
abbrev nativeBaseQValue : NativeBaseCompletion (X := X) :=
  baseQValue (X := X)

/-- The actual base q is nonzero (unconditional object-level fact). -/
theorem nativeBaseQValue_ne_zero : nativeBaseQValue (X := X) ≠ 0 :=
  baseQValue_ne_zero (X := X)

/-- The upper q contraction from the native candidate. -/
theorem nativeUpperQValuation_lt_one :
    (Valued.v (nativeQActual X).q : WithZero (Multiplicative Int)) < 1 :=
  (nativeQActual X).valuation_lt_one

/-- Exact local field norm valuation formula on the actual completion
extension.  This is the missing theorem; it is not assumed globally. -/
def LocalNormValuationFormula : Prop :=
  (Valued.v (nativeBaseQValue (X := X)) : WithZero (Multiplicative Int)) =
    (Valued.v (nativeQActual X).q : WithZero (Multiplicative Int)) ^
      Module.finrank (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X))

/-- The power-monotonicity consequence needed after the valuation formula:
a positive power of a value < 1 is < 1. -/
def PositivePowerContraction : Prop :=
  (Valued.v (nativeQActual X).q : WithZero (Multiplicative Int)) ^
      Module.finrank (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X)) < 1

/-- Object-level contraction target. -/
def NativeQRelativeNormContraction : Prop :=
  (Valued.v (nativeBaseQValue (X := X)) : WithZero (Multiplicative Int)) < 1

/-- Conditional reduction: the local norm valuation formula and positive-power
contraction imply the base q contraction.  Both are explicit goals, not
axioms. -/
theorem nativeQRelativeNormContraction_of_formula
    (hformula : LocalNormValuationFormula (X := X))
    (hpower : PositivePowerContraction (X := X)) :
    NativeQRelativeNormContraction (X := X) := by
  unfold NativeQRelativeNormContraction
  rw [show (Valued.v (nativeBaseQValue (X := X)) :
      WithZero (Multiplicative Int)) =
      (Valued.v (nativeQActual X).q : WithZero (Multiplicative Int)) ^
        Module.finrank (NativeBaseCompletionRaw (X := X))
          (NativeFCompletion (X := X)) from hformula]
  exact hpower

/-- The exact missing local norm theorem: the valuation formula plus the
positive-power contraction step. -/
def LocalNormValuationGap : Prop :=
  LocalNormValuationFormula (X := X) ∧ PositivePowerContraction (X := X)

/-- Conditional full contraction from the exact gap package. -/
theorem nativeQRelativeNormContraction_of_gap
    (h : LocalNormValuationGap (X := X)) :
    NativeQRelativeNormContraction (X := X) :=
  nativeQRelativeNormContraction_of_formula (X := X) h.1 h.2

/-! ## Exact missing object/theorem

Actual objects constructed:

1. baseQValue = relativeNormCompletion (nativeQActual X).q;
2. baseQValue_ne_zero;
3. upper native q valuation < 1.

Missing:

  val_base (relativeNormCompletion q) =
    (val_upper q) ^ [Completion F : Completion Fmod]

together with the positive-power contraction step.  The source does not
provide a local norm valuation/absolute-value formula for Algebra.norm on the
completion extension.  No arbitrary bound or axiom is inserted. -/

end LeanFormal.IUT.XiFPaper.BaseQContractionUnconditional

end
