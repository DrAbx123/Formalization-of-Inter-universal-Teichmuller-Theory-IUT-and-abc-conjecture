import tmp.sheaf.xif.paper.S3096S3097S3098AttemptActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3096S3097S3098AttemptActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S3090S3091CorrectedPlaceActual
open LeanFormal.IUT.XiFPaper.S3092NonBadZeroAttemptActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3096IndexBridgeAttemptActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The source bad index has the two explicit members 5 and 2161. -/
def S3096SourceBadCard : Prop :=
  Fintype.card (Bad (S2696SelectionTwo fiveLabel)) = 2

/-- The native bad index must also have two elements for the bridge. -/
def S3096NativeBadCard : Prop :=
  Fintype.card (Bad (nativePlaceSelection T)) = 2

/-- Conditional index bridge source badPlaces ≃ native Bad, from the two card
equalities. -/
noncomputable def S3096IndexBridge
    (hS : S3096SourceBadCard)
    (hN : S3096NativeBadCard T) :
    Bad (S2696SelectionTwo fiveLabel) ≃ Bad (nativePlaceSelection T) :=
  Fintype.equivOfCardEq (by rw [hS, hN])

/-- S3096 target with the bridge supplied. -/
def S3096PerPlaceOnS3095WithBridge
    (rho : forall v : S3090V,
      (S3090I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).SourceImageRealization v)
    (n : ThetaPilotCarrier fiveLabel)
    (hS : S3096SourceBadCard)
    (hN : S3096NativeBadCard T) : Prop :=
  forall b : Bad (S2696SelectionTwo fiveLabel),
    S3092HullLog
      (S3090I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) rho n
      ((S3090I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.bad_included b) =
      GlobalQVFamThetaHullSumActual.localThetaHullLogFormula T
        (S3096IndexBridge (T := T) hS hN b)

/-- S3097 actual badLabel injectivity implies badIncluded injectivity on the
source partition. -/
theorem S3097_badIncluded_injective_source
    (hlabel : Function.Injective
      (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.partition.badLabel) :
    Function.Injective
      (S2696SourceData fiveLabel R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.partition.badIncluded :=
  S3097_badIncluded_injective _ hlabel

#check S3096SourceBadCard
#check S3096NativeBadCard
#check S3096IndexBridge
#check S3096PerPlaceOnS3095WithBridge
#check S3097_badIncluded_injective_source

end LeanFormal.IUT.XiFPaper.S3096IndexBridgeAttemptActual
end