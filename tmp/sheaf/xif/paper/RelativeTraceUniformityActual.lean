import tmp.sheaf.xif.paper.RelativeTraceCompletionExtension
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace

/-! # Relative trace uniformity from finite-dimensional continuity

relativeTraceOnField : F -> CommonPrimeCompletion Fmod is
x |-> algebraMap Fmod completion (Algebra.trace Fmod F x).

If F and the Fmod-completion are Fmod-normed vector spaces, and F is
finite-dimensional over Fmod, Mathlib's finite-dimensional linear-map continuity
gives a continuous Fmod-linear trace, hence uniform continuity.  This file
constructs that continuous linear map and the resulting RelativeTraceCompletionData.

The needed Fmod-normed structures are not present in the frozen source as global
instances; they are explicit typeclass hypotheses here.  No arbitrary continuity
or axiom is inserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.RelativeTraceUniformityActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual
open LeanFormal.IUT.N8Closure.RelativeTraceCompletionActual
open LeanFormal.IUT.N8Closure.RelativeTraceCompletionExtension

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The Fmod-linear trace map, conditional on the actual Fmod-normed module
structures and finite-dimensionality of F over Fmod. -/
noncomputable def relativeTraceLinearMap
    [NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F]
    [NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    [FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F] :
    X.S.arithmetic.F →L[X.S.arithmetic.Fmod]
      CommonPrimeCompletion (nativeFmodPlaceAtPrime X) where
  toLinearMap :=
    (Algebra.linearMap X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))).comp
      (Algebra.trace X.S.arithmetic.Fmod X.S.arithmetic.F)
  cont := LinearMap.continuous_of_finiteDimensional _

/-- The continuous linear map computes the actual relative trace. -/
theorem relativeTraceLinearMap_apply
    [NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F]
    [NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    [FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F]
    (x : X.S.arithmetic.F) :
    relativeTraceLinearMap (X := X) x = relativeTraceOnField (X := X) x := rfl

/-- Uniform continuity of the actual relative trace, derived from the
continuous Fmod-linear trace map. -/
theorem relativeTraceOnField_uniformContinuous
    [NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F]
    [NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    [FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F] :
    UniformContinuous (relativeTraceOnField (X := X)) := by
  simpa [relativeTraceOnField, relativeTraceLinearMap_apply (X := X)]
    using (relativeTraceLinearMap (X := X)).uniformContinuous

/-- Actual RelativeTraceUniformity object from finite-dimensional continuity. -/
noncomputable def relativeTraceUniformityActual
    [NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F]
    [NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    [FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F] :
    RelativeTraceUniformity (X := X) where
  uniform_continuous := relativeTraceOnField_uniformContinuous (X := X)

/-- Actual relative trace completion data from the finite-dimensional
continuity hypotheses. -/
noncomputable def relativeTraceCompletionDataActual
    [NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F]
    [NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    [FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F] :
    RelativeTraceCompletionData (X := X) :=
  relativeTraceCompletionData (X := X)
    (relativeTraceUniformityActual (X := X))

/-- Unconditional conditional target: the finite-dimensional normed structure
supplies RelativeTraceCompletionData. -/
theorem relativeTraceCompletionDataActual_nonempty
    [NormedSpace X.S.arithmetic.Fmod X.S.arithmetic.F]
    [NormedSpace X.S.arithmetic.Fmod
      (CommonPrimeCompletion (nativeFmodPlaceAtPrime X))]
    [FiniteDimensional X.S.arithmetic.Fmod X.S.arithmetic.F] :
    Nonempty (RelativeTraceCompletionData (X := X)) :=
  ⟨relativeTraceCompletionDataActual (X := X)⟩

/-! ## Exact missing analytic structures

The finite-dimensional linear-map argument is complete as a conditional proof.
The frozen source does not provide, as instances for the actual p-adic
completion topology:

1. NormedSpace Fmod F;
2. NormedSpace Fmod (CommonPrimeCompletion nativeFmodPlaceAtPrime);
3. FiniteDimensional Fmod F (the arithmetic data records finiteFmodF, but no
   NormedSpace structures compatible with the p-adic completion topology).

These are the exact missing analytic structures.  Given them, the trace map is
continuous and hence uniformly continuous, and the RelativeTraceCompletionData
is assembled without arbitrary functions or axioms. -/

end LeanFormal.IUT.XiFPaper.RelativeTraceUniformityActual

end
