import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-! # Relative completion degree and normalized norm

The production norm-transport law is

  ||completionMap a|| = ||a|| ^ relativeCompletionDegree.

If the actual relative completion degree of the native place were 1, the
completion map would be norm-preserving and the scalar action would satisfy the
NormedSpace inequality.  The frozen source does not prove this degree-one
equality; the arithmetic data allow a nontrivial finite extension F/Fmod.

This file records the degree-one target, derives the normed-space compatibility
conditionally, and states the exact missing normalization theorem.  No arbitrary
instance/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.RelativeDegreeNormedActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual relative completion degree of the native F-place over Fmod. -/
def nativeRelativeCompletionDegree : Nat :=
  relativeCompletionDegree (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)

/-- The degree-one target. -/
def RelativeCompletionDegreeOne : Prop :=
  nativeRelativeCompletionDegree (X := X) = 1

/-- Conditional norm preservation from degree one. -/
theorem completionMap_norm_eq_of_degreeOne
    (hdeg : RelativeCompletionDegreeOne (X := X))
    (a : (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion X.S.arithmetic.Fmod)
    (ha : a ≠ 0) :
    ‖completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a‖ = ‖a‖ := by
  have hdeg' : relativeCompletionDegree (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X) = 1 := by
    simpa [RelativeCompletionDegreeOne, nativeRelativeCompletionDegree] using hdeg
  rw [norm_completionMap_pow (k := X.S.arithmetic.Fmod)
    (nativeFPlaceOverBad X) a ha, hdeg']
  simp

/-- Degree one gives the scalar norm inequality for the completion action. -/
theorem completionMap_mul_norm_le_of_degreeOne
    (hdeg : RelativeCompletionDegreeOne (X := X))
    (a : (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion X.S.arithmetic.Fmod)
    (x : (nativeFPlaceOverBad X).maximalIdeal.adicCompletion X.S.arithmetic.F) :
    ‖completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a * x‖ ≤
      ‖a‖ * ‖x‖ := by
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [norm_mul, completionMap_norm_eq_of_degreeOne (X := X) hdeg a ha]

/-- The degree-one condition is the exact normalization needed for the
completion scalar compatibility. -/
def MissingRelativeDegreeOneNormalization : Prop :=
  RelativeCompletionDegreeOne (X := X)

/-! ## Adjusted-norm alternative

An equivalent normalized absolute value on F could be obtained by rescaling
the F-norm by the relative degree.  Constructing that as a NormedField requires
proving the rescaled function is an absolute value and identifying its topology
with the p-adic completion topology.

The exact missing object is:

  AdjustedNormData:
    * a norm ||.||' on F equivalent to the actual p-adic norm;
    * ||algebraMap Fmod F a||' = ||a||_Fmod for all a;
    * NormedField F with this norm (or a NormedSpace Fmod F compatibility).

The frozen source supplies neither the degree-one equality nor the adjusted
norm theorem.  No arbitrary instance/axiom is inserted. -/

end LeanFormal.IUT.XiFPaper.RelativeDegreeNormedActual

end
