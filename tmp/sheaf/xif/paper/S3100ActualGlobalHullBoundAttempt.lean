import tmp.sheaf.xif.paper.S2725GlobalThetaHullActual
import tmp.sheaf.xif.paper.S2807SG3bScalarActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S2711PaperMultiUnconditionalActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.S2807SG3aActual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3100ActualGlobalHullBoundAttempt

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable (D : SourcePilotRegionDonors
  (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat))
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual Haar hull log-volume of the S2725 global theta hull. -/
noncomputable def S3100HullLog
    (D : SourcePilotRegionDonors
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat)) : Real :=
  (globalThetaLogVolume
    (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat D)
    (globalThetaHull
      (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat D))).toReal

/-- The native weighted q-pilot magnitude. -/
noncomputable def S3100QPilotMagnitude : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude (T := T)

/-- S3100 target: actual Haar hull log <= native weighted q magnitude. -/
def S3100GlobalHullBound
    (D : SourcePilotRegionDonors
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat)) : Prop :=
  S3100HullLog R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat D ≤
  S3100QPilotMagnitude T

/-- The hull log is the negative S2717 theta hull log. -/
theorem S3100_hullLog_eq_neg_theta
    (D : SourcePilotRegionDonors
      (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat)) :
    S3100HullLog R redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat D =
    - S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat
      places tuple nu D := by
  unfold S3100HullLog globalThetaLogVolume
  rw [S2807_thetaHullVolume_eq_neg_tensorLogVolume]
  simp only [globalThetaHull_eq_imageSet, globalThetaImageSet,
    actualC3LogShellTensorLogVolume]
  ring

#check S3100HullLog
#check S3100QPilotMagnitude
#check S3100GlobalHullBound
#check S3100_hullLog_eq_neg_theta

end LeanFormal.IUT.XiFPaper.S3100ActualGlobalHullBoundAttempt
end