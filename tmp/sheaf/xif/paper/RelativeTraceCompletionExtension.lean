import tmp.sheaf.xif.paper.RelativeTraceCompletionActual
import Mathlib.Analysis.Normed.Group.Completion

/-! # Relative trace completion extension

The actual relative trace on the number fields is

  Algebra.trace Fmod F : F -> Fmod,

and its dense-field image is

  relativeTraceOnField : F -> CommonPrimeCompletion Fmod.

Mathlib's uniform completion extension constructs the continuous extension

  UniformSpace.Completion.extension relativeTraceOnField

from the F-completion to the Fmod-completion as soon as relativeTraceOnField
is uniformly continuous.  This file performs that construction and records the
uniform continuity of the actual relative trace as the exact missing analytic
input.  No arbitrary map/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure
namespace RelativeTraceCompletionExtension

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FToFmodMapActual
open LeanFormal.IUT.N8Closure.RelativeTraceCompletionActual

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The exact analytic input: uniform continuity of the actual relative trace
on the dense field F.  This is what the continuous-linear-map/field-trace
argument must supply. -/
structure RelativeTraceUniformity where
  uniform_continuous : UniformContinuous (relativeTraceOnField (X := X))

/-- The actual completion extension constructed by Mathlib's uniform
completion extension from the dense field trace. -/
noncomputable def relativeTraceCompletion
    (U : RelativeTraceUniformity (X := X)) :
    FCompletion (X := X) → FmodCompletion (X := X) :=
  UniformSpace.Completion.extension (relativeTraceOnField (X := X))
    U.uniform_continuous

/-- The extension is continuous. -/
theorem relativeTraceCompletion_continuous
    (U : RelativeTraceUniformity (X := X)) :
    Continuous (relativeTraceCompletion (X := X) U) :=
  UniformSpace.Completion.continuous_extension (f := relativeTraceOnField (X := X)) (hf := U.uniform_continuous)

/-- The extension agrees with the actual relative trace on the dense field
image. -/
theorem relativeTraceCompletion_algebraMap
    (U : RelativeTraceUniformity (X := X)) (x : X.S.arithmetic.F) :
    relativeTraceCompletion (X := X) U
        (algebraMap X.S.arithmetic.F (FCompletion (X := X)) x) =
      relativeTraceOnField (X := X) x :=
  UniformSpace.Completion.extension_coe (f := relativeTraceOnField (X := X)) U.uniform_continuous x

/-- Actual RelativeTraceCompletionData assembled from the dense trace and its
uniform continuity. -/
noncomputable def relativeTraceCompletionData
    (U : RelativeTraceUniformity (X := X)) :
    RelativeTraceCompletionData (X := X) where
  trace := relativeTraceCompletion (X := X) U
  trace_continuous := relativeTraceCompletion_continuous (X := X) U
  trace_algebraMap := by
    intro x
    rw [relativeTraceCompletion_algebraMap (X := X) U x]
    rfl

/-- The assembled data yields the F-completion -> Fmod-completion map. -/
noncomputable def relativeTraceCompletionToFmodMap
    (U : RelativeTraceUniformity (X := X)) :
    FCompletionToFmodCompletionMap (X := X) :=
  relativeTraceToFmodMap (X := X)
    (relativeTraceCompletionData (X := X) U)

/-- The exact missing theorem: uniform continuity of the actual relative trace
on F, equivalently the continuous Fmod-linear trace extension to the
F-completion. -/
def MissingRelativeTraceUniformity : Prop :=
  Nonempty (RelativeTraceUniformity (X := X))

/-- Conditional construction: the missing uniformity supplies the full trace
completion data and the F -> Fmod map. -/
theorem relativeTraceCompletionData_nonempty_of_uniformity
    (h : MissingRelativeTraceUniformity (X := X)) :
    Nonempty (RelativeTraceCompletionData (X := X)) := by
  rcases h with ⟨U⟩
  exact ⟨relativeTraceCompletionData (X := X) U⟩

/-! ## Exact missing analytic theorem

Actual data:
1. Algebra.trace Fmod F on the number fields;
2. the dense-field map relativeTraceOnField : F -> CommonPrimeCompletion Fmod;
3. Mathlib's uniform completion extension, conditional on uniform continuity.

Missing:
  UniformContinuous (relativeTraceOnField) (equivalently continuity/uniform
  continuity of the Fmod-linear relative trace on the finite extension), and
  its compatibility with algebraMap is then automatic by extension_coe.

No arbitrary function/axiom is chosen. -/

end RelativeTraceCompletionExtension
end LeanFormal.IUT.N8Closure

end
