import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3112BaseQIdentityActual

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- With Fmod = F (the concrete Gaussian boundary), the native F-place over the
bad base place is the bad base place itself. -/
theorem S3112_place_eq
    (hA : X.S.arithmetic.Fmod = X.S.arithmetic.F) :
    nativeFPlaceOverBad X = nativeBadBasePlace X := by
  subst hA
  have h := nativeFPlaceOverBad_comap X
  simpa using h

end LeanFormal.IUT.XiFPaper.S3112BaseQIdentityActual
end