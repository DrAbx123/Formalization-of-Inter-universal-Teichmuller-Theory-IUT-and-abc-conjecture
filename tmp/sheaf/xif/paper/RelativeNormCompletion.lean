import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-! # CONDITIONAL STATUS (xi-f)

Constructs the actual Algebra.norm relative norm map, but the q-specific nonzero/valuation<1 evaluation is missing; no unconditional base q.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Relative norm on completions from the actual local field extension

The production file FinitePlaceCompletionNormTransport supplies:

* completionAlgebra : the upper completion as an algebra over the lower
  completion, induced by the actual completion embedding;
* moduleFinite_completionAlgebra : the upper completion is a finite module over
  the lower completion.

Therefore Algebra.norm over the lower completion is available on the upper
completion.  This file constructs that relative norm map.  The base completion
is the completion of comap(nativeFPlaceOverBad) = nativeBadBasePlace; the final
map is obtained by casting along that actual place equality.

The map is actual.  Its two q-candidate laws for nativeQActual (nonzero and
valuation < 1) are not derivable from the norm formula alone and remain the
exact missing local norm evaluation.  No arbitrary map/axiom/sorry is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.RelativeNormCompletion

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The native F-completion. -/
abbrev NativeFCompletion : Type :=
  NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X)

/-- The raw base completion, indexed by the comap place. -/
abbrev NativeBaseCompletionRaw : Type :=
  NumberFieldFinitePlace.Completion
    (NumberFieldFinitePlace.comap (k := X.S.arithmetic.Fmod)
      (nativeFPlaceOverBad X))

/-- The actual base completion at the bad base place. -/
abbrev NativeBaseCompletion : Type :=
  NumberFieldFinitePlace.Completion (nativeBadBasePlace X)

/-- The upper completion as an algebra over the lower (raw) completion. -/
noncomputable abbrev relativeCompletionAlgebra :
    Algebra (NativeBaseCompletionRaw (X := X)) (NativeFCompletion (X := X)) :=
  completionAlgebra (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)

/-- The upper completion is a finite module over the lower completion. -/
theorem relativeCompletionModuleFinite :
    letI := relativeCompletionAlgebra (X := X)
    Module.Finite (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) :=
  moduleFinite_completionAlgebra (k := X.S.arithmetic.Fmod)
    (nativeFPlaceOverBad X)

/-- The actual relative norm on completions, before casting the base place
equality. -/
noncomputable def relativeNormRaw :
    NativeFCompletion (X := X) → NativeBaseCompletionRaw (X := X) :=
  letI := relativeCompletionAlgebra (X := X)
  haveI : Module.Finite (NativeBaseCompletionRaw (X := X))
      (NativeFCompletion (X := X)) :=
    relativeCompletionModuleFinite (X := X)
  fun x => Algebra.norm (NativeBaseCompletionRaw (X := X)) x

/-- The actual relative norm on completions, with codomain the native bad base
completion, using comap(nativeFPlaceOverBad) = nativeBadBasePlace. -/
noncomputable def relativeNormCompletion :
    NativeFCompletion (X := X) → NativeBaseCompletion (X := X) :=
  fun x =>
    cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
      NumberFieldFinitePlace.Completion p)
      (nativeFPlaceOverBad_comap X)) (relativeNormRaw (X := X) x)

/-- The relative norm is the algebra norm after casting. -/
theorem relativeNormCompletion_apply (x : NativeFCompletion (X := X)) :
    relativeNormCompletion (X := X) x =
      cast (congrArg (fun p : NumberField.FinitePlace X.S.arithmetic.Fmod =>
        NumberFieldFinitePlace.Completion p)
        (nativeFPlaceOverBad_comap X)) (relativeNormRaw (X := X) x) := rfl

/-- The exact missing q-candidate laws for the constructed relative norm. -/
structure RelativeNormQProperties where
  q_ne_zero : relativeNormCompletion (X := X) (nativeQActual X).q ≠ 0
  valuation_lt_one :
    (Valued.v (relativeNormCompletion (X := X) (nativeQActual X).q) :
      WithZero (Multiplicative Int)) < 1

/-- Construct the base q candidate once the exact norm-evaluation laws are
supplied for the actual native q. -/
noncomputable def baseQCandidateOfRelativeNorm
    (P : RelativeNormQProperties (X := X)) :
    FinitePlaceQCandidate (nativeBadBasePlace X) where
  q := relativeNormCompletion (X := X) (nativeQActual X).q
  q_ne_zero := P.q_ne_zero
  valuation_lt_one := P.valuation_lt_one

/-- The constructed q is the relative norm of nativeQActual. -/
@[simp] theorem baseQCandidateOfRelativeNorm_q
    (P : RelativeNormQProperties (X := X)) :
    (baseQCandidateOfRelativeNorm (X := X) P).q =
      relativeNormCompletion (X := X) (nativeQActual X).q := rfl

/-! ## Exact missing local norm evaluation

The relative norm map itself is constructed from the actual
completionAlgebra and moduleFinite_completionAlgebra.

Not derivable from the current norm formula:

1. relativeNormCompletion (nativeQActual X).q != 0;
2. valuation (relativeNormCompletion (nativeQActual X).q) < 1.

The production norm transport law applies to images of base-field elements
(completionMap x), not to the arbitrary completion element nativeQActual.q.
Proving these two q-specific laws requires the local norm evaluation of the
Tate q, which is the exact missing norm construction/law. -/

end LeanFormal.IUT.XiFPaper.RelativeNormCompletion

end
