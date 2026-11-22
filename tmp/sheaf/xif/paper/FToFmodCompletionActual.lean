import tmp.sheaf.xif.paper.RelativeNormCompletion
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource

/-!
# Actual F-completion -> Fmod-completion map: relative norm

The actual completion extension is

  NativeFCompletion = Completion (nativeFPlaceOverBad X)          over
  NativeBaseCompletion = Completion (nativeBadBasePlace X).

RelativeNormCompletion constructs the actual relative algebra norm

  relativeNormCompletion : NativeFCompletion -> NativeBaseCompletion.

The base place as a CommonPrimeCompletion is exactly nativeC3Place X, whose
underlying place is nativeBadBasePlace X by construction.  Therefore the actual
relative norm is an actual map

  Completion (nativeFPlaceOverBad X) ->
    CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X).

It is multiplicative (an algebra norm); it is NOT a ring hom / additive
completion restriction.  The opposite-direction completion restriction
(completionMap from the Fmod completion to the F completion) exists, but no
actual additive/ring-theoretic F-completion -> Fmod-completion descent map is
constructed in the tree.  That is the exact missing map if an additive descent
(rather than the relative norm) is required.

No arbitrary map is chosen.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.FToFmodCompletionActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual relative norm as a map from the F-completion to the Fmod
CommonPrimeCompletion at the native base place. -/
def fToFmodCompletion :
    NativeFCompletion (X := X) ->
      CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X) :=
  fun x => relativeNormCompletion (X := X) x

/-- The map is the actual relative norm. -/
theorem fToFmodCompletion_apply (x : NativeFCompletion (X := X)) :
    fToFmodCompletion (X := X) x =
      relativeNormCompletion (X := X) x := rfl

/-- The actual q image in the Fmod completion. -/
noncomputable def nativeQBaseImage :
    CommonPrimeCompletion (K := X.S.arithmetic.Fmod) (nativeC3Place X) :=
  fToFmodCompletion (X := X) (nativeQActual X).q

/-- The q image is the relative algebra norm of the actual native q. -/
theorem nativeQBaseImage_eq :
    nativeQBaseImage (X := X) =
      relativeNormCompletion (X := X) (nativeQActual X).q := rfl

/-- The actual available map is the relative algebra norm, which is multiplicative
by construction but not an additive ring descent.  If an additive/ring F -> Fmod
map is required, it is the exact missing object. -/
def MissingAdditiveFToFmodDescent : Prop :=
  Nonempty (NativeFCompletion (X := X) →+ CommonPrimeCompletion
    (K := X.S.arithmetic.Fmod) (nativeC3Place X))

end LeanFormal.IUT.XiFPaper.FToFmodCompletionActual

end