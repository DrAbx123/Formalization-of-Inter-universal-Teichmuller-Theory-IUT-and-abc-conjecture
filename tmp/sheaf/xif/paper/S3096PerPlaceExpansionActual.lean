import tmp.sheaf.xif.paper.S3096S3097S3098AttemptActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3096S3097S3098AttemptActual
open LeanFormal.IUT.XiFPaper.S3092NonBadZeroAttemptActual
open LeanFormal.IUT.XiFPaper.S3090S3091CorrectedPlaceActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
namespace LeanFormal.IUT.XiFPaper.S3096PerPlaceExpansionActual

variable (R : S1280RemainingClauses S2771FiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (T : SourceNativeInitialThetaData.{0} S2771FiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

abbrev S3096PI : OriginalInput S2771FiveLabel S3090V :=
  S3096I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- Per-place expansion: the source hull log at badToV b is the actual local
qVFamily theta-hull formula at e b. -/
def S3096PerPlaceExpansion
    (rho : forall v : S3090V, (S3096PI R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).SourceImageRealization v)
    (n : ThetaPilotCarrier S2771FiveLabel)
    (e : (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces
        ≃ Bad (nativePlaceSelection T)) : Prop :=
  forall b : (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces,
    S3092HullLog (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat) rho n
      (S3090_badToV R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat b) =
    localThetaHullLogFormula T (e b)

theorem S3096PerPlaceExpansion_iff
    (rho : forall v : S3090V, (S3096PI R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).SourceImageRealization v)
    (n : ThetaPilotCarrier S2771FiveLabel)
    (e : (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces
        ≃ Bad (nativePlaceSelection T)) :
    S3096PerPlaceExpansion R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat T rho n e ↔
      forall b : (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces,
        S3092HullLog (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat) rho n
          (S3090_badToV R redCompat hredCompat torCompat htorCompat orbCompat
            horbCompat secCompat hsecCompat cusCompat hcusCompat b) =
        localThetaHullLogFormula T (e b) :=
  Iff.rfl

#check S3096PI
#check S3096PerPlaceExpansion
#check S3096PerPlaceExpansion_iff

end LeanFormal.IUT.XiFPaper.S3096PerPlaceExpansionActual