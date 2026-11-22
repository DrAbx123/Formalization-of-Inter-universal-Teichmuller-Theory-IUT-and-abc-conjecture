import tmp.sheaf.xif.paper.RelativeNormCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open scoped WithZero
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion

namespace LeanFormal.IUT.XiFPaper.NormalizedNormValuationResidueActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Correct local norm valuation power law: the exponent is the residue degree
`f` of the completion extension, not the full degree `e * f` (`finrank`).  The
`finrank` exponent version is false for ramified `e > 1`; see the totally
ramified quadratic example `K = ℚ_p(√p)` where `N(√p) = -p` has valuation one
while `finrank = 2`. -/
def AlgebraNormValuationPowerResidue : Prop :=
  ∀ x : NativeFCompletion (X := X), x ≠ 0 →
    (Valued.v (relativeNormCompletion (X := X) x) : WithZero (Multiplicative ℤ)) =
      (Valued.v x) ^ relativeResidueDegree (k := ℚ) (nativeFPlaceOverBad X)

/-- The object-level contraction target for the base q. -/
def NativeQRelativeNormContraction : Prop :=
  (Valued.v (relativeNormCompletion (X := X) (nativeQActual X).q) :
    WithZero (Multiplicative ℤ)) < 1

/-- The residue-degree power law implies contraction of the base q (positive
power of an upper contraction remains `< 1`). -/
theorem nativeQRelativeNormContraction_of_residue_power
    (h : AlgebraNormValuationPowerResidue (X := X)) :
    NativeQRelativeNormContraction (X := X) := by
  unfold NativeQRelativeNormContraction
  rw [h (nativeQActual X).q (nativeQActual X).q_ne_zero]
  exact pow_lt_one₀ bot_le (nativeQActual X).valuation_lt_one
    (relativeResidueDegree_ne_zero (k := ℚ) (nativeFPlaceOverBad X))

end LeanFormal.IUT.XiFPaper.NormalizedNormValuationResidueActual