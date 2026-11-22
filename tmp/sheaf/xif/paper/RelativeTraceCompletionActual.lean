import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.LinearAlgebra.Trace

/-! # Relative trace: actual field map and exact missing completion extension

This file is self-contained for the relative-trace group.  It defines the actual
F-completion/Fmod-completion aliases and the exact missing comparison map, then
the actual dense-field relative trace and the missing completion extension
record.  No toy/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w

/-- The actual Fmod base place under the native bad moduli place. -/
abbrev nativeFmodBasePlace {l : PrimeGeFive} (X : N8NativeInput l) :
    NumberField.FinitePlace X.S.arithmetic.Fmod :=
  nativeBadBasePlace X

/-- The rational prime under the Fmod base place. -/
noncomputable def nativePrimeFmod {l : PrimeGeFive} (X : N8NativeInput l) : Nat :=
  (completionRationalPrime (nativeFmodBasePlace X)).val

/-- The prime fact for the Fmod base place. -/
instance nativePrimeFmodFact {l : PrimeGeFive} (X : N8NativeInput l) :
    Fact (Nat.Prime (nativePrimeFmod X)) :=
  ⟨(completionRationalPrime (nativeFmodBasePlace X)).property⟩

/-- The actual Fmod base place as a FinitePlaceAtPrime. -/
noncomputable def nativeFmodPlaceAtPrime {l : PrimeGeFive} (X : N8NativeInput l) :
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativePrimeFmod X) :=
  ⟨nativeFmodBasePlace X, rfl⟩

namespace FToFmodMapActual

/-- The actual F-completion at the native F-place over the bad moduli place. -/
abbrev FCompletion {l : PrimeGeFive} (X : N8NativeInput l) : Type :=
  Completion (nativeFPlaceOverBad X)

/-- The actual Fmod-completion at the native base place. -/
abbrev FmodCompletion {l : PrimeGeFive} (X : N8NativeInput l) : Type :=
  CommonPrimeCompletion (nativeFmodPlaceAtPrime X)

/-- The actual embedding of the base field into its completion, used as the
Algebra structure in the relative-trace statements. -/
noncomputable instance fmodCompletionAlgebra {l : PrimeGeFive} (X : N8NativeInput l) :
    Algebra X.S.arithmetic.Fmod (FmodCompletion X) :=
  (NumberField.FinitePlace.embedding (NumberFieldFinitePlace.underlyingPrime (nativeFmodPlaceAtPrime X).val)).toAlgebra

/-- Exact missing source comparison: an F-completion -> Fmod-completion map at
the native base place. -/
structure FCompletionToFmodCompletionMap {l : PrimeGeFive} (X : N8NativeInput l) where
  toFmod : FCompletion X → FmodCompletion X

/-- Exact missing analytic object: a continuous Fmod-linear trace extension from
the F-completion to the Fmod-completion, compatible with the actual relative
trace on the dense field image. -/
structure RelativeTraceCompletionData {l : PrimeGeFive} (X : N8NativeInput l) where
  trace : FCompletion X → FmodCompletion X
  trace_continuous : Continuous trace
  trace_algebraMap : forall x : X.S.arithmetic.F,
    trace (algebraMap X.S.arithmetic.F (FCompletion X) x) =
      algebraMap X.S.arithmetic.Fmod (FmodCompletion X)
        (Algebra.trace X.S.arithmetic.Fmod X.S.arithmetic.F x)

/-- The actual F-completion -> Fmod-completion map supplied by the exact
relative-trace completion object. -/
noncomputable def relativeTraceToFmodMap {l : PrimeGeFive} (X : N8NativeInput l)
    (T : RelativeTraceCompletionData X) :
    FCompletionToFmodCompletionMap X :=
  { toFmod := T.trace }

/-- The exact missing relative-trace completion supplies the F -> Fmod map. -/
theorem fCompletionToFmodMap_of_relativeTrace {l : PrimeGeFive} (X : N8NativeInput l)
    (T : RelativeTraceCompletionData X) :
    Nonempty (FCompletionToFmodCompletionMap X) :=
  ⟨relativeTraceToFmodMap X T⟩

end FToFmodMapActual

namespace RelativeTraceCompletionActual

open LeanFormal.IUT.N8Closure.FToFmodMapActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual relative trace on the two number fields, followed by the actual
algebraMap into the Fmod-completion. -/
noncomputable def relativeTraceOnField (x : X.S.arithmetic.F) :
    FmodCompletion X :=
  algebraMap X.S.arithmetic.Fmod (FmodCompletion X)
    (Algebra.trace X.S.arithmetic.Fmod X.S.arithmetic.F x)

/-- The actual dense-field value of the relative trace at the image of x. -/
theorem relativeTraceOnField_apply (x : X.S.arithmetic.F) :
    relativeTraceOnField X x =
      algebraMap X.S.arithmetic.Fmod (FmodCompletion X)
        (Algebra.trace X.S.arithmetic.Fmod X.S.arithmetic.F x) :=
  rfl

/-- The exact missing theorem as a proposition: existence of a continuous
completion extension of the actual relative trace, compatible with algebraMap
on the dense field image. -/
def RelativeTraceCompletionExtensionTheorem : Prop :=
  Nonempty (RelativeTraceCompletionData X)

/-- The exact missing theorem supplies the F -> Fmod map. -/
theorem fCompletionToFmodMap_of_extensionTheorem
    (h : RelativeTraceCompletionExtensionTheorem X) :
    Nonempty (FCompletionToFmodCompletionMap X) :=
  h.elim (fun T => fCompletionToFmodMap_of_relativeTrace X T)

/-- The fields required of any actual relative trace completion extension. -/
structure RelativeTraceCompletionExtension where
  data : RelativeTraceCompletionData X
  extends_map : forall x : X.S.arithmetic.F,
    data.trace (algebraMap X.S.arithmetic.F (FCompletion X) x) =
      relativeTraceOnField X x

/-- The exact missing extension object is equivalently an extension whose trace
agrees with the actual relative trace on the dense field image. -/
theorem relativeTraceCompletionExtension_nonempty_iff :
    Nonempty (RelativeTraceCompletionExtension X) ↔
      RelativeTraceCompletionExtensionTheorem X := by
  constructor
  · rintro ⟨E⟩
    exact ⟨E.data⟩
  · rintro ⟨T⟩
    exact ⟨{ data := T, extends_map := T.trace_algebraMap }⟩

/-- Exact missing theorem: the actual relative trace has a continuous
completion extension with the displayed algebraMap compatibility. -/
def MissingRelativeTraceCompletionTheorem : Prop :=
  Nonempty (RelativeTraceCompletionExtension X)

/-- From the exact missing extension theorem one gets the F -> Fmod map. -/
theorem fCompletionToFmodMap_of_missingTheorem
    (h : MissingRelativeTraceCompletionTheorem X) :
    Nonempty (FCompletionToFmodCompletionMap X) :=
  fCompletionToFmodMap_of_extensionTheorem X
    ((relativeTraceCompletionExtension_nonempty_iff X).mp h)

end RelativeTraceCompletionActual
end LeanFormal.IUT.N8Closure
end
