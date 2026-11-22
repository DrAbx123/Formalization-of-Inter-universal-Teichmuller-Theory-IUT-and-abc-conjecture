import tmp.sheaf.xif.paper.RelativeNormCompletion
import tmp.sheaf.xif.paper.BaseQUnconditionalActual

/-! # Relative norm contraction on the native q

The actual base q is baseQValue = relativeNormCompletion (nativeQActual X).q.
This file records the exact local norm/valuation formula needed to prove

  (Valued.v (baseQValue X) : WithZero (Multiplicative Int)) < 1.

The available production facts are:

* (nativeQActual X).valuation_lt_one, the upper q contraction;
* the relative norm is Algebra.norm on the actual finite completion algebra.

What is missing is the local field norm valuation formula

  v_base (Norm_{F/Fmod}(q)) = v_upper(q) ^ [F : Fmod],

or equivalently the corresponding formula for the absolute norm.  Without it,
contraction of the upper q does not imply contraction of the base relative norm
in the frozen tree.  No arbitrary bound/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.RelativeNormContractionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.BaseQUnconditionalActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual base q value. -/
abbrev nativeBaseQValue : NativeBaseCompletion (X := X) :=
  baseQValue (X := X)

/-- The actual upper q contraction. -/
theorem nativeUpperQValuation_lt_one :
    (Valued.v (nativeQActual X).q : WithZero (Multiplicative Int)) < 1 :=
  (nativeQActual X).valuation_lt_one

/-- The exact missing local field norm valuation formula.  The exponent is the
actual degree of the completion extension. -/
def RelativeNormValuationFormula : Prop :=
  (Valued.v (nativeBaseQValue (X := X)) : WithZero (Multiplicative Int)) =
    (Valued.v (nativeQActual X).q : WithZero (Multiplicative Int)) ^
      Module.finrank (NativeBaseCompletionRaw (X := X))
        (NativeFCompletion (X := X))

/-- The object-level contraction target. -/
def NativeQRelativeNormContraction : Prop :=
  (Valued.v (nativeBaseQValue (X := X)) : WithZero (Multiplicative Int)) < 1

/-- The missing formula is exactly what is not present: no local norm
valuation formula on completions is in the frozen source. -/
def RelativeNormValuationGap : Prop :=
  RelativeNormValuationFormula (X := X)

/-! ## Exact missing local norm formula

Required object-level formula:

  val_base (relativeNormCompletion q) =
    (val_upper q) ^ [Completion F : Completion Fmod].

The source provides:
1. val_upper nativeQActual.q < 1;
2. the relative norm as Algebra.norm;
3. Module.Finite of the completion algebra.

It does not provide the norm-valuation formula (or the absolute-value norm
formula) transporting the contraction through Algebra.norm.  That formula is
the exact missing local norm theorem. -/

end LeanFormal.IUT.XiFPaper.RelativeNormContractionActual

end
