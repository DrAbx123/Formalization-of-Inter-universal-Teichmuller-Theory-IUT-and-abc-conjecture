import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-! # CONDITIONAL STATUS (xi-f)

Conditional on BaseQNormData / relative norm; no reverse local norm evaluation.

This module is NOT an unconditional target closure. Do not use it as evidence that paper xi-f is proved; read its exact Missing declarations and the audit ledger.
-/


/-! # Base q by relative norm/restriction

The native q is a FinitePlaceQCandidate at the F-place nativeFPlaceOverBad X.
The C3 base donor needs a q at the base place nativeBadBasePlace X.

The production norm-transport file proves, for the canonical embedding

  completionMap : Completion base -> Completion F,

that the upper norm is the lower norm raised to the relative completion degree.
This is a norm formula in the base-to-extension direction.  The required object
is the reverse relative norm/restriction

  Norm_{F/Fmod} : Completion (nativeFPlaceOverBad X) ->
    Completion (nativeBadBasePlace X),

together with nonvanishing and contraction of the native q image.  No such
relative norm on completions, and no proof that nativeQActual is in the image of
completionMap, is present in the frozen tree.

No arbitrary q/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.BaseQNormActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The rational prime of the native bad base place. -/
def nativeBasePrime : Nat :=
  (completionRationalPrime (nativeBadBasePlace X)).val

/-- The actual prime fact. -/
theorem nativeBasePrime_prime : Nat.Prime (nativeBasePrime X) :=
  (completionRationalPrime (nativeBadBasePlace X)).property

/-- The actual base place. -/
def nativeBasePlace :
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeBasePrime X) :=
  ⟨nativeBadBasePlace X, rfl⟩

/-- The native F-completion. -/
abbrev NativeFCompletion : Type :=
  Completion (nativeFPlaceOverBad X)

/-- The native base completion. -/
abbrev NativeBaseCompletion : Type :=
  Completion (nativeBadBasePlace X)

/-- The exact missing relative-norm package. -/
structure BaseQNormData where
  normCompletion : NativeFCompletion (X := X) → NativeBaseCompletion (X := X)
  q_ne_zero : normCompletion (nativeQActual X).q ≠ 0
  valuation_lt_one :
    (Valued.v (normCompletion (nativeQActual X).q) :
      WithZero (Multiplicative Int)) < 1

/-- Construct the base q candidate from the explicit relative-norm package. -/
def baseQCandidateOfNorm
    (D : BaseQNormData (X := X)) :
    FinitePlaceQCandidate (nativeBadBasePlace X) where
  q := D.normCompletion (nativeQActual X).q
  q_ne_zero := D.q_ne_zero
  valuation_lt_one := D.valuation_lt_one

/-- The constructed q is the relative norm of the native q. -/
@[simp] theorem baseQCandidateOfNorm_q
    (D : BaseQNormData (X := X)) :
    (baseQCandidateOfNorm (X := X) D).q =
      D.normCompletion (nativeQActual X).q := rfl

/-- The actual native q at the F-place. -/
def nativeFQCandidate :
    FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  nativeQActual X

/-! ## Exact missing relative norm/restriction

Required:

  normCompletion : Completion (nativeFPlaceOverBad X) ->
    Completion (nativeBadBasePlace X)

with:
1. normCompletion (nativeQActual X).q != 0;
2. valuation (normCompletion (nativeQActual X).q) < 1.

The source has completionMap only in the opposite (base -> F) direction and
proves norm transport only for images of base elements.  There is no relative
norm on the extension completion and no proof that the native q lies in the
image of completionMap, so no unconditional base q candidate is constructed. -/

end LeanFormal.IUT.XiFPaper.BaseQNormActual

end
