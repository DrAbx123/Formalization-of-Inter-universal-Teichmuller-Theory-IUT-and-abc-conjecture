import tmp.sheaf.xif.paper.S2562C3CompletionDirectionActual
import tmp.sheaf.xif.paper.S2563C3BaseQNonzeroActual
import tmp.sheaf.xif.paper.S2565ValuativeExtensionActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.RelativeNormCompletion
open LeanFormal.IUT.XiFPaper.S2562C3CompletionDirectionActual
open LeanFormal.IUT.XiFPaper.S2563C3BaseQNonzeroActual
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.S2566C3BaseQCastActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem S2566Cast_ne_zero
    {K : Type*} [Field K] [NumberField K]
    {p q : NumberField.FinitePlace K} (h : p = q)
    (x : NumberFieldFinitePlace.Completion p) (hx : x ≠ 0) :
    cast (congrArg (fun r => NumberFieldFinitePlace.Completion r) h) x ≠ 0 := by
  cases h
  exact hx

theorem S2566BaseQValue_ne_zero : S2562BaseQValue X ≠ 0 := by
  unfold S2562BaseQValue S2562FToBaseNormMap relativeNormCompletion
  exact S2566Cast_ne_zero (nativeFPlaceOverBad_comap X)
    (relativeNormRaw (X := X) (nativeQActual X).q)
    (S2563RelativeNormRaw_ne_zero X)

noncomputable def S2566BaseQCandidateOfContraction
    (hcontr : (Valued.v (S2562BaseQValue X) : WithZero (Multiplicative Int)) < 1) :
    FinitePlaceQCandidate (nativeBadBasePlace X) :=
  S2562BaseQCandidateOfLaws X (S2566BaseQValue_ne_zero X) hcontr

#check S2566BaseQValue_ne_zero
#check S2566BaseQCandidateOfContraction
#print axioms S2566BaseQValue_ne_zero
#print axioms S2566BaseQCandidateOfContraction
end LeanFormal.IUT.XiFPaper.S2566C3BaseQCastActual
end