import tmp.sheaf.xif.paper.FmodTensorLandingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.LinearAlgebra.Trace

/-!
# F-completion -> Fmod-completion map: actual construction attempt

The previous file reduced the Fmod tensor landing to the exact map
FCompletionToFmodCompletionMap. This file tries to construct that map from
actual relative trace/norm and completion algebra data.

The actual candidate is the continuous Fmod-linear trace of the finite field
extension F/Fmod, extended to the F-completion. The production tree has:

* the actual Fmod base place and F place over it;
* the actual algebra Fmod -> F and its finite-dimensional/Galois instances;
* the actual completions Completion(F) and CommonPrimeCompletion(Fmod).

It does NOT contain a theorem extending the relative trace
Algebra.trace Fmod F to the completions, nor a compatibility of that extension
with algebraMap. Therefore the map is constructed conditionally from an
explicit RelativeTraceCompletionData record, and the exact missing object is
recorded. No arbitrary function, choice from countability, axiom, or sorry is
used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace FToFmodMapActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.FmodTensorLandingActual
open MeasureTheory

universe u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual F-completion at the native F-place over the bad moduli place. -/
abbrev FCompletion : Type :=
  Completion (nativeFPlaceOverBad X)

/-- The actual Fmod-completion at the native base place. -/
abbrev FmodCompletion : Type :=
  CommonPrimeCompletion (nativeFmodPlaceAtPrime X)

/-- Actual Fmod-algebra structure on the normalized completion, transported
from the actual `Fmod -> Completion` algebra along the normalized-completion
ring equivalence. -/
noncomputable instance fmodCompletionAlgebra :
    Algebra X.S.arithmetic.Fmod (FmodCompletion (X := X)) :=
  ((normalizedCompletionRingEquiv (nativeFmodPlaceAtPrime X).val).symm.toRingHom.comp
    (algebraMap X.S.arithmetic.Fmod
      (Completion (nativeFmodPlaceAtPrime X).val))).toAlgebra

/-- Exact missing analytic object: a continuous Fmod-linear trace extension
from the F-completion to the Fmod-completion, compatible with the actual
relative trace on the dense field image. -/
structure RelativeTraceCompletionData where
  trace : FCompletion (X := X) → FmodCompletion (X := X)
  trace_continuous : Continuous trace
  trace_algebraMap : forall x : X.S.arithmetic.F,
    trace (algebraMap X.S.arithmetic.F (FCompletion (X := X)) x) =
      algebraMap X.S.arithmetic.Fmod (FmodCompletion (X := X))
        (Algebra.trace X.S.arithmetic.Fmod X.S.arithmetic.F x)

/-- The actual F-completion -> Fmod-completion map supplied by the exact
relative-trace completion object. -/
noncomputable def relativeTraceToFmodMap
    (T : RelativeTraceCompletionData (X := X)) :
    FCompletionToFmodCompletionMap (X := X) :=
  { toFmod := T.trace }

/-- The exact missing relative-trace completion supplies the F -> Fmod map. -/
theorem fCompletionToFmodMap_of_relativeTrace
    (T : RelativeTraceCompletionData (X := X)) :
    Nonempty (FCompletionToFmodCompletionMap (X := X)) :=
  ⟨relativeTraceToFmodMap X T⟩

/-- Exact missing object: a relative trace extension from the actual
F-completion to the actual Fmod-completion. -/
def MissingRelativeTraceCompletion : Prop :=
  Nonempty (RelativeTraceCompletionData (X := X))

/-- The F -> Fmod map is exactly reduced to the missing relative trace. -/
theorem fCompletionToFmodMap_required :
    MissingRelativeTraceCompletion (X := X) ->
      Nonempty (FCompletionToFmodCompletionMap (X := X)) :=
  fun h => h.elim (fun T => fCompletionToFmodMap_of_relativeTrace X T)

/-- The actual Fmod base place data remains available; only the completion map
is missing. -/
theorem nativeFmodPlaceAtPrime_available :
    Nonempty (FinitePlaceAtPrime X.S.arithmetic.Fmod (nativePrimeFmod X)) :=
  ⟨nativeFmodPlaceAtPrime X⟩

end FToFmodMapActual
end LeanFormal.IUT.N8Closure
end
