import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.xif.paper.S3102CorrectedC3Actual
import tmp.sheaf.xif.paper.S3094ActualQFamilyAttempt

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3102CorrectedC3Actual
open LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3106DonorWithNativeIndexAttempt

variable {l : PrimeGeFive} {V : Type}
variable (I : OriginalInput l V)

/-- Exact donor target. -/
def S3106DonorTarget : Prop :=
  Nonempty (SourcePilotRegionDonors (l := l) (V := V) I)

/-- Every tensor place of a donor lies over the single donor prime p. -/
theorem S3106_tensorPlace_prime
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (i : D.tensorIndex) (j : D.tensorPlaceIndex i) :
    (completionRationalPrime (D.tensorPlaces i j).val).val = D.p :=
  (D.tensorPlaces i j).2

/-- Two tensor places with different rational primes cannot both live in one
donor. -/
theorem S3106_two_prime_conflict
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (i₁ : D.tensorIndex) (j₁ : D.tensorPlaceIndex i₁)
    (i₂ : D.tensorIndex) (j₂ : D.tensorPlaceIndex i₂)
    (h5 : (completionRationalPrime (D.tensorPlaces i₁ j₁).val).val = 5)
    (h2161 : (completionRationalPrime (D.tensorPlaces i₂ j₂).val).val = 2161) :
    False := by
  have h1 := S3106_tensorPlace_prime I D i₁ j₁
  have h2 := S3106_tensorPlace_prime I D i₂ j₂
  omega

#check S3106DonorTarget
#check S3106_tensorPlace_prime
#check S3106_two_prime_conflict

end LeanFormal.IUT.XiFPaper.S3106DonorWithNativeIndexAttempt
end