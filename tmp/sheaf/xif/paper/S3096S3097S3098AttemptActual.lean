import tmp.sheaf.xif.paper.S3095ActualQOriginalInputAttempt
import tmp.sheaf.xif.paper.S3092NonBadZeroAttemptActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3095ActualQOriginalInputAttempt
open LeanFormal.IUT.XiFPaper.S3092NonBadZeroAttemptActual
open LeanFormal.IUT.XiFPaper.S3090S3091CorrectedPlaceActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3096S3097S3098AttemptActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The corrected source input used for the source-side hull logs. -/
noncomputable abbrev S3096I : OriginalInput fiveLabel S3090V :=
  S3090I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- S3096 target: on the corrected input, the hull log at badToV b equals the
local qVFamily formula. -/
def S3096PerPlaceOnS3095
    (rho : forall v : S3090V, S3096I R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat |>.SourceImageRealization v)
    (n : ThetaPilotCarrier fiveLabel)
    (e : (S3096I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces
        ≃ Bad (nativePlaceSelection T)) : Prop :=
  forall b : (S3096I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces,
    S3092HullLog (S3096I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat) rho n
      (S3090_badToV R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat b) =
    GlobalQVFamThetaHullSumActual.localThetaHullLogFormula T (e b)

/-- S3097: badIncluded is injective whenever badLabel is injective. -/
theorem S3097_badIncluded_injective
    {Selected Bad : Type}
    (P : SourcePlacePartition Selected Bad)
    (hlabel : Function.Injective P.badLabel) :
    Function.Injective P.badIncluded := by
  intro b1 b2 h
  apply hlabel
  rw [← P.badLabel_compatible b1, ← P.badLabel_compatible b2, h]

/-- S3097 target for the actual partition. -/
def S3097BadToVInjective : Prop :=
  Function.Injective
    (S3090_badToV R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat)

/-- S3098 target: non-bad places have zero hull log. -/
def S3098NonBadZero
    (rho : forall v : S3090V, S3096I R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat |>.SourceImageRealization v)
    (n : ThetaPilotCarrier fiveLabel) : Prop :=
  forall v : S3090V,
    v ∉ Set.range (S3090_badToV R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) ->
    S3092HullLog (S3096I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat) rho n v = 0

#check S3096PerPlaceOnS3095
#check S3097_badIncluded_injective
#check S3097BadToVInjective
#check S3098NonBadZero

end LeanFormal.IUT.XiFPaper.S3096S3097S3098AttemptActual
end