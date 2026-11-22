import tmp.sheaf.xif.paper.RelativeTraceUniformityActual
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # Normed-space data for the relative trace extension

The finite-dimensional trace-continuity proof needs F and the Fmod-completion
to be Fmod-normed vector spaces, with F finite-dimensional over Fmod.  The
frozen source does not provide those NormedSpace instances for the actual
p-adic completion topology.  This file records the exact package and the
conditional consequences; it does not fabricate instances. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.RelativeTraceNormedSpaceActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeTraceUniformityActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact NormedSpace/NormedField/finiteness package needed by the
finite-dimensional trace continuity proof. -/
structure RelativeTraceNormedData where
  normedFieldFmod : NormedField X.S.arithmetic.Fmod
  normedFieldF : NormedField X.S.arithmetic.F
  normedSpaceBase : NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F
  normedFieldCompletion : NormedField
    (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))
  normedSpaceCompletion : NormedSpace X.S.arithmetic.Fmod
    (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))
  finiteDimensional : FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F

attribute [instance] RelativeTraceNormedData.normedFieldFmod
attribute [instance] RelativeTraceNormedData.normedFieldF
attribute [instance] RelativeTraceNormedData.normedSpaceBase
attribute [instance] RelativeTraceNormedData.normedFieldCompletion
attribute [instance] RelativeTraceNormedData.normedSpaceCompletion
attribute [instance] RelativeTraceNormedData.finiteDimensional

/-- The NormedSpace package yields the uniform continuity of the actual
relative trace. -/
theorem relativeTraceOnField_uniformContinuous_of_normedData
    (D : RelativeTraceNormedData (X := X)) :
    UniformContinuous (relativeTraceOnField (X := X)) := by
  letI := D.normedFieldFmod
  letI := D.normedFieldF
  letI := D.normedSpaceBase
  letI := D.normedFieldCompletion
  letI := D.normedSpaceCompletion
  letI := D.finiteDimensional
  exact relativeTraceOnField_uniformContinuous (X := X)

/-- The NormedSpace package yields actual RelativeTraceCompletionData. -/
noncomputable def relativeTraceCompletionData_of_normedData
    (D : RelativeTraceNormedData (X := X)) :
    RelativeTraceCompletionData (X := X) := by
  letI := D.normedFieldFmod
  letI := D.normedFieldF
  letI := D.normedSpaceBase
  letI := D.normedFieldCompletion
  letI := D.normedSpaceCompletion
  letI := D.finiteDimensional
  exact relativeTraceCompletionDataActual (X := X)

/-- The exact missing package. -/
def RelativeTraceNormedDataGap : Prop :=
  Nonempty (RelativeTraceNormedData (X := X))

/-- Conditional completion from the exact missing NormedSpace package. -/
theorem relativeTraceCompletionData_nonempty_of_normedData
    (h : RelativeTraceNormedDataGap (X := X)) :
    Nonempty (RelativeTraceCompletionData (X := X)) := by
  rcases h with ⟨D⟩
  exact ⟨relativeTraceCompletionData_of_normedData (X := X) D⟩

/-! ## Exact missing instances

1. NormedSpace Fmod F;
2. NormedSpace Fmod (CommonPrimeCompletion nativeFmodPlaceAtPrime);
3. FiniteDimensional Fmod F paired with those norm structures.

No arbitrary instance/axiom is inserted. -/

end LeanFormal.IUT.XiFPaper.RelativeTraceNormedSpaceActual

end
