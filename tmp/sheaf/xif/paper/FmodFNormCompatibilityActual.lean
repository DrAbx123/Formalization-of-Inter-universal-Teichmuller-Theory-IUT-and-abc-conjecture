import tmp.sheaf.xif.paper.NormedSpaceFmodFActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-! # Fmod-F norm compatibility from the embedded base norm bound

For the actual p-adic NormedField structures, the scalar action is

  a • x = algebraMap Fmod F a * x,

so multiplicativity of the F-norm gives

  ||a • x||_F = ||algebraMap Fmod F a||_F * ||x||_F.

The NormedSpace inequality therefore follows from the single embedded-base
norm bound

  ||algebraMap Fmod F a||_F <= ||a||_Fmod.

The frozen source does not prove this bound: the base and extension
Valued.toNormedField structures are normalized independently.  This file proves
the reduction and records the exact missing norm relation.  No arbitrary
inequality/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.FmodFNormCompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual
open LeanFormal.IUT.XiFPaper.ValuedNormedInstancesActual
open LeanFormal.IUT.XiFPaper.NormedSpaceFmodFActual

universe ua uv upi umon ui uF uG

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact embedded-base norm bound needed for the NormedSpace inequality. -/
structure EmbeddedBaseNormBound
    (Fmod : Type uF) (F : Type uG) [NormedField Fmod] [NormedField F]
    [Algebra Fmod F] where
  bound : ∀ a : Fmod, ‖algebraMap Fmod F a‖ ≤ ‖a‖

/-- Multiplicativity reduces the NormedSpace inequality to the embedded-base
norm bound. -/
theorem norm_smul_le_of_embedding_bound
    {Fmod : Type uF} {F : Type uG} [NormedField Fmod] [NormedField F]
    [Algebra Fmod F] (D : EmbeddedBaseNormBound Fmod F)
    (a : Fmod) (x : F) :
    ‖a • x‖ ≤ ‖a‖ * ‖x‖ := by
  rw [Algebra.smul_def, norm_mul]
  exact mul_le_mul_of_nonneg_right (D.bound a) (norm_nonneg x)

/-- The embedded-base norm bound supplies the FmodFNormCompatibility package. -/
noncomputable def fmodFNormCompatibility_of_embedding_bound
    {Fmod : Type uF} {F : Type uG} [NormedField Fmod] [NormedField F]
    [Algebra Fmod F] (D : EmbeddedBaseNormBound Fmod F) :
    FmodFNormCompatibility Fmod F where
  norm_smul_le := fun a x => norm_smul_le_of_embedding_bound D a x

/-- Exact missing relation: the embedded base element has F-norm bounded by its
Fmod-norm. -/
def MissingEmbeddedBaseNormBound : Prop :=
  Nonempty (EmbeddedBaseNormBound X.S.arithmetic.Fmod X.S.arithmetic.F
    (nativeFmodNormedField (X := X)) (nativeFNormedField (X := X)))

/-- The missing relation is sufficient for the conditional NormedSpace. -/
theorem nativeNormedSpaceFmodF_of_embedding_bound
    (h : MissingEmbeddedBaseNormBound (X := X)) :
    Nonempty (FmodFNormCompatibility X.S.arithmetic.Fmod X.S.arithmetic.F
      (nativeFmodNormedField (X := X)) (nativeFNormedField (X := X))) := by
  rcases h with ⟨D⟩
  exact ⟨fmodFNormCompatibility_of_embedding_bound D⟩

/-! ## Exact missing norm relation

Required:

  forall a : Fmod,
    ||algebraMap Fmod F a||_F <= ||a||_Fmod.

Source facts:
1. Algebra.smul_def gives a • x = algebraMap a * x;
2. F is a NormedField, so ||a • x|| = ||algebraMap a|| * ||x||.

Missing: the comparison of the two independently normalized p-adic absolute
values on the embedded base.  Without it the multiplier inequality is not
derivable.  No arbitrary inequality/axiom is inserted. -/


/-! ## Completion-map norm correction

For the actual completion embedding, production proves

  ||completionMap a|| = ||a|| ^ relativeCompletionDegree.

If ||a|| <= 1 and the relative degree is at least one, then
||completionMap a|| <= ||a||.  This gives the multiplier inequality for
contracting scalars in the completion.  It does NOT give the full NormedSpace
inequality for all a: for ||a|| > 1 and degree > 1, the power is larger than
||a||, so the inequality reverses.  This is the exact obstruction. -/

section CompletionMap

open LeanFormal.IUT.NumberFieldFinitePlace

variable {k K : Type*} [Field k] [Field K] [NumberField k] [NumberField K]
  [Algebra k K] [IsScalarTower ℚ k K]

/-- Contracting completion-map norm bound from the production norm-transport
formula. -/
theorem completionMap_norm_le_of_norm_le_one
    (place : NumberField.FinitePlace K)
    (a : (NumberFieldFinitePlace.comap (k := k) place).maximalIdeal.adicCompletion k)
    (ha : ‖a‖ ≤ 1)
    (hd : 1 ≤ relativeCompletionDegree (k := k) place) :
    ‖completionMap (k := k) place a‖ ≤ ‖a‖ := by
  by_cases h : a = 0
  · subst h
    simp
  · rw [norm_completionMap_pow (k := k) place a h]
    calc
      ‖a‖ ^ relativeCompletionDegree (k := k) place ≤ ‖a‖ ^ 1 :=
        pow_le_pow_left₀ (norm_nonneg a) ha hd
      _ = ‖a‖ := pow_one ‖a‖

/-- The multiplier inequality for contracting completion scalars. -/
theorem completionMap_mul_norm_le_of_norm_le_one
    (place : NumberField.FinitePlace K)
    (a : (NumberFieldFinitePlace.comap (k := k) place).maximalIdeal.adicCompletion k)
    (x : place.maximalIdeal.adicCompletion K)
    (ha : ‖a‖ ≤ 1)
    (hd : 1 ≤ relativeCompletionDegree (k := k) place) :
    ‖completionMap (k := k) place a * x‖ ≤ ‖a‖ * ‖x‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (completionMap_norm_le_of_norm_le_one (k := k) place a ha hd)
    (norm_nonneg x)

/-- Exact obstruction to extending the inequality to all scalars: the
completion-map norm is a positive power of the base norm, so for base norm > 1
and relative degree > 1 the direction reverses. -/
def CompletionMapNormObstruction : Prop :=
  ∃ (place : NumberField.FinitePlace K)
    (a : (NumberFieldFinitePlace.comap (k := k) place).maximalIdeal.adicCompletion k),
    1 < ‖a‖ ∧ 1 < relativeCompletionDegree (k := k) place ∧
      ‖a‖ < ‖completionMap (k := k) place a‖

end CompletionMap

end LeanFormal.IUT.XiFPaper.FmodFNormCompatibilityActual

end
