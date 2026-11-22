import tmp.sheaf.xif.paper.S3082S3083AttemptActual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3082S3083AttemptActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullSumActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3084S3085AttemptActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

/-- S3084 target: the finite rational prime strip V = FinitePrimePlace 2 7 is
the source selected-places type. -/
def S3084PlaceEquiv : Prop :=
  Nonempty (FinitePrimePlace 2 7 ≃
    (S2711I R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.selectedPlaces)

/-- The actual V is the rational prime strip 2..7. -/
def S3084V : Type := FinitePrimePlace 2 7

/-- The actual selectedPlaces type is the subtype of source field places. -/
def S3084Selected : Type :=
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat).initial.selectedPlaces

/-- S3085 target: per-place hull log equals the qVFamily local formula. -/
def S3085PerPlaceHullFormula
    (I : OriginalInput fiveLabel (FinitePrimePlace 2 7))
    (R : forall v : FinitePrimePlace 2 7, I.SourceImageRealization v)
    (n : ThetaPilotCarrier fiveLabel)
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    (e : FinitePrimePlace 2 7 ≃ Bad (nativePlaceSelection T)) : Prop :=
  forall v : FinitePrimePlace 2 7,
    Real.log (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal =
      GlobalQVFamThetaHullSumActual.localThetaHullLogFormula T (e.toFun v)

#check S3084PlaceEquiv
#check S3084V
#check S3084Selected
#check S3085PerPlaceHullFormula

end LeanFormal.IUT.XiFPaper.S3084S3085AttemptActual
end