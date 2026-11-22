import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.n8.closure.NativeC3

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3113PlaceIdentityActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

theorem S3113_place_eq
    (hA : X.S.arithmetic.Fmod = X.S.arithmetic.F) :
    cast (congrArg (fun T => NumberField.FinitePlace T) hA.symm)
      (nativeFPlaceOverBad X) = nativeBadBasePlace X := by
  cases hA
  simpa using nativeFPlaceOverBad_comap X

#check S3113_place_eq
#print axioms S3113_place_eq

end LeanFormal.IUT.XiFPaper.S3113PlaceIdentityActual
end