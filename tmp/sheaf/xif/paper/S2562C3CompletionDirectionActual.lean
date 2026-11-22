import tmp.sheaf.xif.paper.RelativeNormCompletion
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import LeanFormal.IUT.Foundations.NumberField.FinitePlaceExtension

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.S2562C3CompletionDirectionActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual base -> F embedding of completions at the native bad place. -/
noncomputable def S2562BaseToFCompletionMap :
    (comap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)).maximalIdeal.adicCompletion
      X.S.arithmetic.Fmod →+*
      (nativeFPlaceOverBad X).maximalIdeal.adicCompletion X.S.arithmetic.F :=
  completionMap (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)

theorem S2562BaseToFCompletionMap_injective :
    Function.Injective (S2562BaseToFCompletionMap X) :=
  completionMap_injective (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)

/-- Actual F -> base relative norm on completions (multiplicative norm map). -/
noncomputable def S2562FToBaseNormMap :
    NativeFCompletion (X := X) → NativeBaseCompletion (X := X) :=
  relativeNormCompletion (X := X)

/-- The actual base q value: relative norm of the native F-place q. -/
noncomputable def S2562BaseQValue : NativeBaseCompletion (X := X) :=
  S2562FToBaseNormMap X (nativeQActual X).q

/-- Conditional base q candidate from the actual relative norm, given the
nonzero and contraction laws (exact remaining local norm evaluation). -/
noncomputable def S2562BaseQCandidateOfLaws
    (hq : S2562BaseQValue X ≠ 0)
    (hcontr : (Valued.v (S2562BaseQValue X) : WithZero (Multiplicative Int)) < 1) :
    FinitePlaceQCandidate (nativeBadBasePlace X) where
  q := S2562BaseQValue X
  q_ne_zero := hq
  valuation_lt_one := hcontr

#check S2562BaseToFCompletionMap
#check S2562FToBaseNormMap
#check S2562BaseQCandidateOfLaws
#print axioms S2562FToBaseNormMap
#print axioms S2562BaseQCandidateOfLaws
end LeanFormal.IUT.XiFPaper.S2562C3CompletionDirectionActual
end