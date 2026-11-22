import tmp.sheaf.xif.paper.RelativeNormCompletion

/-!
# Algebra norm valuation power theorem: conditional proof and exact missing theorem

For the actual finite completion extension

  NativeBaseCompletion = Completion (comap (nativeFPlaceOverBad X))
  NativeFCompletion    = Completion (nativeFPlaceOverBad X)

the actual relative norm is Algebra.norm, packaged as
relativeNormCompletion in RelativeNormCompletion.lean.

A finite extension of nonarchimedean local fields satisfies the valuation power
law

  exists n > 0, forall x != 0,
    Valued.v (relativeNormCompletion x) = (Valued.v x)^n,

with n the relative degree/ramification factor in the chosen normalization.
This is the exact general norm/valuation theorem missing from the tree.

Below, the law is stated as an explicit theorem target; the contraction of the
actual native q is proved conditionally on it.  No arbitrary formula, exponent,
or inequality is asserted.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.AlgebraNormValuationActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact valuation power law for the actual algebra norm. -/
def AlgebraNormValuationPower (n : Nat) : Prop :=
  0 < n ∧ forall (x : NativeFCompletion (X := X)), x ≠ 0 ->
    Valued.v (relativeNormCompletion (X := X) x) =
      (Valued.v x) ^ n

/-- Exact missing general theorem: the algebra norm has a positive valuation
power law.  No exponent is selected. -/
def MissingAlgebraNormValuationPowerTheorem : Prop :=
  exists n : Nat, AlgebraNormValuationPower (X := X) n

/-- The native q relative norm contraction target. -/
def NativeQRelativeNormContraction : Prop :=
  (Valued.v (relativeNormCompletion (X := X) (nativeQActual X).q) :
    WithZero (Multiplicative Int)) < 1

/-- Conditional contraction from the exact valuation power law. -/
theorem nativeQRelativeNormContraction_of_power
    (n : Nat) (h : AlgebraNormValuationPower (X := X) n) :
    NativeQRelativeNormContraction (X := X) := by
  rcases h with ⟨hnpos, hformula⟩
  unfold NativeQRelativeNormContraction
  rw [hformula (nativeQActual X).q (nativeQActual X).q_ne_zero]
  exact pow_lt_one₀ bot_le (nativeQActual X).valuation_lt_one hnpos.ne'

/-- Conditional contraction from the existential missing theorem. -/
theorem nativeQRelativeNormContraction_of_missing
    (h : MissingAlgebraNormValuationPowerTheorem (X := X)) :
    NativeQRelativeNormContraction (X := X) := by
  rcases h with ⟨n, hpow⟩
  exact nativeQRelativeNormContraction_of_power (X := X) n hpow

/-- The exact missing theorem is equivalent to the existential power-law form
used by the contraction consumer. -/
theorem missing_iff_exists_power :
    MissingAlgebraNormValuationPowerTheorem (X := X) ↔
      exists n : Nat, AlgebraNormValuationPower (X := X) n :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.AlgebraNormValuationActual

end