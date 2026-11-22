import tmp.sheaf.xif.paper.CompletionNormedFiniteActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Completion NormedSpace via the norm inequality

Task-691 write-only attempt.

A Mathlib NormedSpace only requires the inequality
  ‖a • x‖ ≤ ‖a‖ * ‖x‖
(not equality). The actual scalar action on completions is
  a • x = completionMap a * x,
so
  ‖a • x‖ = ‖completionMap a‖ * ‖x‖
           = ‖a‖ ^ relativeCompletionDegree * ‖x‖
when a is nonzero.

Therefore the inequality holds whenever
  (H1) every base-completion scalar has norm at most one;
  (H2) relativeCompletionDegree ≥ 1.

This file constructs the actual NormedSpace structure from H1/H2 and the
actual completion algebra/trace data, and proves the finite-dimensional
instance from moduleFinite_completionAlgebra.

Exact remaining hypothesis: BaseNormLeOne, i.e.
  forall a, ‖a‖ ≤ 1.
This is not a theorem for the full p-adic completion (elements with negative
valuation have norm greater than one). If a base element has norm >1 and the
relative degree is >1, the standard inequality fails for x=1, so the standard
NormedSpace instance is obstructed. No nonstandard scalar norm is invented.

No arbitrary instance/True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.CompletionNormedSpaceInequalityAdapted

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.CompletionNormedFiniteActual

universe u v

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact missing bounded-scalar hypothesis. -/
def BaseNormLeOne : Prop :=
  ∀ a : NativeBaseCompletionRaw (X := X), ‖a‖ ≤ 1

/-- The relative degree is at least one. -/
theorem nativeRelativeCompletionDegree_ge_one :
    1 ≤ nativeRelativeCompletionDegree (X := X) := by
  exact Nat.succ_le_of_lt
    (relativeCompletionDegree_pos (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X))

/-- The actual norm-scalar inequality for the completion scalar action. -/
theorem completion_norm_smul_le
    (hbound : BaseNormLeOne (X := X)) :
    ∀ (a : NativeBaseCompletionRaw (X := X))
      (x : NativeFCompletion (X := X)),
      ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  intro a x
  letI := relativeCompletionAlgebra (X := X)
  by_cases ha : a = 0
  · subst ha
    simp
  · have hsmul := completionAlgebra_smul
      (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a x
    have hpow := norm_completionMap_pow
      (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X) a ha
    have hcast : ‖completionMap (k := X.S.arithmetic.Fmod)
        (nativeFPlaceOverBad X) a‖ =
        ‖a‖ ^ nativeRelativeCompletionDegree (X := X) := by
      simpa [nativeRelativeCompletionDegree] using hpow
    have hle : ‖a‖ ^ nativeRelativeCompletionDegree (X := X) ≤ ‖a‖ := by
      exact pow_le_of_le_one (norm_nonneg a)
        (hbound a) (Nat.ne_of_lt (relativeCompletionDegree_pos
          (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)))
    calc ‖a • x‖ = ‖completionMap (k := X.S.arithmetic.Fmod)
          (nativeFPlaceOverBad X) a * x‖ := by rw [hsmul]
      _ = ‖completionMap (k := X.S.arithmetic.Fmod)
            (nativeFPlaceOverBad X) a‖ * ‖x‖ := norm_mul _ _
      _ = ‖a‖ ^ nativeRelativeCompletionDegree (X := X) * ‖x‖ := by
            rw [hcast]
      _ ≤ ‖a‖ * ‖x‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg x)

/-- The actual conditional NormedSpace structure on the F-completion over the
base completion, from the exact bounded-scalar hypothesis. -/
noncomputable def completionNormedSpace
    (hbound : BaseNormLeOne (X := X)) :
    NormedSpace (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) where
  toModule := by
    letI := relativeCompletionAlgebra (X := X)
    infer_instance
  norm_smul_le := completion_norm_smul_le (X := X) hbound

/-- The conditional NormedSpace is the actual completion scalar action. -/
theorem completionNormedSpace_norm_smul_le
    (hbound : BaseNormLeOne (X := X))
    (a : NativeBaseCompletionRaw (X := X))
    (x : NativeFCompletion (X := X)) :
    ‖a • x‖ ≤ ‖a‖ * ‖x‖ :=
  completionNormedSpace (X := X) hbound |>.norm_smul_le a x

/-- Exact status: under BaseNormLeOne, both NormedSpace and FiniteDimensional
are constructed; without it the standard norm-scalar inequality is obstructed
for scalars of norm greater than one. -/
theorem completionNormedSpaceInequality_status
    (hbound : BaseNormLeOne (X := X)) :
    Nonempty (NormedSpace (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))) ∧
    @FiniteDimensional (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) _ _ (relativeCompletionModule (X := X)) :=
  ⟨⟨completionNormedSpace (X := X) hbound⟩,
    completionFiniteDimensional⟩

/-- The exact obstruction witness for the standard inequality: a base scalar
with norm greater than one and relative degree greater than one would violate
the required norm-scalar inequality at x = 1. -/
def StandardNormScalarObstruction : Prop :=
  (∃ a : NativeBaseCompletionRaw (X := X), 1 < ‖a‖) ∧
    1 < nativeRelativeCompletionDegree (X := X)

end LeanFormal.IUT.XiFPaper.CompletionNormedSpaceInequalityAdapted

end
