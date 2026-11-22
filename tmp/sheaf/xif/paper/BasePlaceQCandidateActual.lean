import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-! # Base-place q candidate from the native F-place q

NativeC3.nativeQActual is a FinitePlaceQCandidate at

  nativeFPlaceOverBad X : NumberField.FinitePlace X.S.arithmetic.F.

The C3 donor record needs a q candidate at the base place

  nativeBadBasePlace X : NumberField.FinitePlace X.S.arithmetic.Fmod.

There is a canonical completionMap from the base completion to the extension
completion, and norm transport identities for that embedding.  The frozen tree
does not provide a reverse restriction/norm/descent map from the extension
completion to the base completion.  This file therefore constructs the base q
candidate only from an explicit descent package and records that package as the
exact missing local map.  No arbitrary q or axiom is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The rational prime of the native selected bad base place. -/
def nativeBasePrime : Nat :=
  (completionRationalPrime (nativeBadBasePlace X)).val

/-- The actual prime fact for the native bad base place. -/
theorem nativeBasePrime_prime : Nat.Prime (nativeBasePrime X) :=
  (completionRationalPrime (nativeBadBasePlace X)).property

/-- The native bad base place as a FinitePlaceAtPrime. -/
def nativeBasePlace :
    FinitePlaceAtPrime X.S.arithmetic.Fmod (nativeBasePrime X) :=
  ⟨nativeBadBasePlace X, rfl⟩

/-- The extension completion of the native F-place. -/
abbrev NativeFCompletion : Type :=
  NumberFieldFinitePlace.Completion (nativeFPlaceOverBad X)

/-- The base completion of the native bad base place. -/
abbrev NativeBaseCompletion : Type :=
  NumberFieldFinitePlace.Completion (nativeBadBasePlace X)

/-- The exact missing local map package: a descent from the native F-completion
to the base completion which sends the native q to a nonzero, contracting
base q.  Norm transport in the repository goes from base to extension, not in
this direction. -/
structure BaseQDescentData where
  descent : NativeFCompletion (X := X) → NativeBaseCompletion (X := X)
  q_ne_zero : descent (nativeQActual X).q ≠ 0
  valuation_lt_one :
    (Valued.v (descent (nativeQActual X).q) : WithZero (Multiplicative Int)) < 1

/-- Construct the base-place q candidate from the explicit descent package. -/
def baseQCandidateOfDescent
    (D : BaseQDescentData (X := X)) :
    FinitePlaceQCandidate (nativeBadBasePlace X) where
  q := D.descent (nativeQActual X).q
  q_ne_zero := D.q_ne_zero
  valuation_lt_one := D.valuation_lt_one

/-- The constructed q is the descent image of the actual native q. -/
@[simp] theorem baseQCandidateOfDescent_q
    (D : BaseQDescentData (X := X)) :
    (baseQCandidateOfDescent (X := X) D).q =
      D.descent (nativeQActual X).q := rfl

/-- The actual native q candidate at the F-place. -/
def nativeFQCandidate :
    FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  nativeQActual X


/-! ## Exact missing local map

The required object is a map

  descent : Completion (nativeFPlaceOverBad X) ->
    Completion (nativeBadBasePlace X)

with the two q-candidate laws for descent (nativeQActual X).q:

1. nonzero;
2. valuation < 1.

The available production map is completionMap in the opposite direction
(base -> extension).  No norm/restriction/descent map in the extension -> base
direction, and no proof that the native q descends, is present.  Consequently
BaseQDescentData is the exact missing package and no base q candidate is
constructed unconditionally. -/

end LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual

end
