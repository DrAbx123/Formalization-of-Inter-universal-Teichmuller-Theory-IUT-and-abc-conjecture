import tmp.sheaf.xif.paper.AdditiveFToFmodActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Continuity of the actual relative-trace F -> Fmod additive map

Task-670 write-only attempt.

The actual additive map relativeTraceFmodAddHom from AdditiveFToFmodActual is
built from the algebra trace of the completion algebra:
  Algebra.trace (Completion (comap F-place)) (Completion F-place).

A finite-dimensional linear map between normed spaces over a complete normed
field is continuous. Thus continuity follows from the actual completion
algebra and finite module structure, provided the missing normed-space /
finite-dimensional instances are supplied:

  NormedSpace (Completion (comap F-place)) (Completion F-place)
  FiniteDimensional (Completion (comap F-place)) (Completion F-place)

The production tree supplies completionAlgebra and moduleFinite_completionAlgebra,
but not the normed-space scalar structure nor the finite-dimensional instance.
This file proves the conditional continuity theorem and records those instances
as the exact missing data. No arbitrary continuity assertion is added.

No arbitrary map/True/PUnit, axiom, or sorry is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.RelativeTraceContinuityActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.AdditiveFToFmodActual

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Conditional continuity of the raw relative trace from the exact missing
normed-space and finite-dimensional instances. -/
theorem relativeTraceRawAddHom_continuous
    [NormedSpace (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))]
    [FiniteDimensional (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))] :
    Continuous (relativeTraceRawAddHom (X := X)) := by
  letI := relativeCompletionAlgebra (X := X)
  haveI : Module.Finite (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) :=
    relativeCompletionModuleFinite (X := X)
  haveI : Module.Free (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) :=
    Module.Free.of_divisionRing
  change Continuous (fun x : NativeFCompletion (X := X) =>
    Algebra.trace (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) x)
  exact (Algebra.trace (NativeBaseCompletionRaw (X := X))
    (NativeFCompletion (X := X))).continuous_of_finiteDimensional

/-- Conditional continuity of the cast relative-trace map. -/
theorem relativeTraceCompletionAddHom_continuous
    [NormedSpace (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))]
    [FiniteDimensional (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))] :
    Continuous (relativeTraceCompletionAddHom (X := X)) := by
  have hraw := relativeTraceRawAddHom_continuous (X := X)
  cases nativeFPlaceOverBad_comap (X := X)
  simpa [relativeTraceCompletionAddHom] using hraw

/-- Conditional continuity of the actual F -> Fmod additive map. -/
theorem relativeTraceFmodAddHom_continuous
    [NormedSpace (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))]
    [FiniteDimensional (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X))] :
    Continuous (relativeTraceFmodAddHom (X := X)) := by
  have hcast := relativeTraceCompletionAddHom_continuous (X := X)
  have hnorm : Continuous (fun x : NativeBaseCompletion (X := X) =>
      (normalizedCompletionRingEquiv (nativeBadBasePlace (X := X))).symm x) := by
    simpa [normalizedCompletionRingEquiv] using
      (continuous_id : Continuous (id : NativeBaseCompletion (X := X) →
        NativeBaseCompletion (X := X)))
  simpa [relativeTraceFmodAddHom] using hnorm.comp hcast

/-- The exact missing normed-space instance. -/
def MissingRelativeTraceNormedSpace : Prop :=
  Nonempty (NormedSpace (NativeBaseCompletionRaw (X := X))
    (NativeFCompletion (X := X)))

/-- The exact missing finite-dimensional instance. -/
def MissingRelativeTraceFiniteDimensional : Prop :=
  Nonempty (FiniteDimensional (NativeBaseCompletionRaw (X := X))
    (NativeFCompletion (X := X)))

/-- Exact missing data package for continuity of the relative trace. -/
structure MissingRelativeTraceContinuityInstances : Prop where
  normedSpace : MissingRelativeTraceNormedSpace (X := X)
  finiteDimensional : MissingRelativeTraceFiniteDimensional (X := X)

end LeanFormal.IUT.N8Closure.RelativeTraceContinuityActual

end
