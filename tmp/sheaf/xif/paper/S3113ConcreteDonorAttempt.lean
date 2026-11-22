import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.xif.paper.C3DonorFieldsFromSource
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.BasePlaceQCandidateActual
open LeanFormal.IUT.XiFPaper.C3DonorFieldsFromSource
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3113ConcreteDonorAttempt

variable (X : N8NativeInput fiveLabel)
variable (I : OriginalInput fiveLabel (FinitePrimePlace 2 7))

/-- Exact concrete donor target. -/
def S3113ConcreteDonorTarget : Prop :=
  Nonempty (SourcePilotRegionDonors (l := fiveLabel) (V := FinitePrimePlace 2 7) I)

/-- The actual native base place (Fmod side). -/
abbrev S3113Place : FinitePlaceAtPrime (X.S.arithmetic.Fmod) (nativeC3Prime X) :=
  nativeC3Place X

/-- The actual native q at the F place. -/
abbrev S3113Q : FinitePlaceQCandidate (nativeFPlaceOverBad X) :=
  nativeQActual X

#check S3113ConcreteDonorTarget
#check S3113Place
#check S3113Q
#check nativeC3Prime_prime
#check nativeQActual

end LeanFormal.IUT.XiFPaper.S3113ConcreteDonorAttempt
end