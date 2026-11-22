import tmp.sheaf.xif.paper.S3089CorrectedOriginalInputActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullSumActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3089CorrectedOriginalInputActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3090S3091CorrectedPlaceActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

/-- The corrected V: the selected places type. -/
abbrev S3090V : Type := S3089Selected

/-- The corrected input. -/
noncomputable abbrev S3090I : OriginalInput fiveLabel S3090V :=
  S3089CorrectedOriginalInput R redCompat hredCompat torCompat htorCompat
    orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

/-- Actual equivalence V ≃ initial.selectedPlaces, by refl. -/
noncomputable def S3090_selectedEquiv :
    S3090V ≃ (S3090I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.selectedPlaces :=
  Equiv.refl _

/-- Actual bad-to-V inclusion (the direction provided by bad_included). -/
noncomputable def S3090_badToV :
    (S3090I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).initial.badPlaces → S3090V :=
  fun b =>
    (S3090I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).initial.bad_included b

/-- S3091 exact target, parameterized by a chosen selected-to-bad map. -/
def S3091PerPlaceFormula
    (rho : forall v : S3090V,
      (S3090I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat).SourceImageRealization v)
    (n : ThetaPilotCarrier fiveLabel)
    (T : SourceNativeInitialThetaData fiveLabel)
    (f : S3090V → Bad (nativePlaceSelection T)) : Prop :=
  forall v : S3090V,
    Real.log
      ((S3090I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).sourceSetVolume v
        ((S3090I R redCompat hredCompat torCompat htorCompat orbCompat
          horbCompat secCompat hsecCompat cusCompat hcusCompat).sourceHolomorphicHull v
          (rho v) n)).toReal =
      GlobalQVFamThetaHullSumActual.localThetaHullLogFormula T (f v)

#check S3090V
#check S3090_selectedEquiv
#check S3090_badToV
#check S3091PerPlaceFormula

end LeanFormal.IUT.XiFPaper.S3090S3091CorrectedPlaceActual
end