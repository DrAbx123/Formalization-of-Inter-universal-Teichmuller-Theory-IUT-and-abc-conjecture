import tmp.sheaf.xif.paper.S3096PerPlaceExpansionActual
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

namespace LeanFormal.IUT.XiFPaper.S3096FirstError

variable (R : S1280RemainingClauses S2771FiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (T : SourceNativeInitialThetaData.{0} S2771FiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (rho : forall v : S3090V, (S3096PI R redCompat hredCompat torCompat htorCompat
  orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).SourceImageRealization v)
variable (n : ThetaPilotCarrier S2771FiveLabel)
variable (e : (S3096PI R redCompat hredCompat torCompat htorCompat orbCompat
  horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces
    ≃ Bad (nativePlaceSelection T))

theorem attempt : S3096PerPlaceExpansion R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat T rho n e := by
  intro b
  unfold S3092HullLog localThetaHullLogFormula

end LeanFormal.IUT.XiFPaper.S3096FirstError
