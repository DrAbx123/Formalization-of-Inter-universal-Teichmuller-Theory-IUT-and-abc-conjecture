import tmp.sheaf.xif.paper.S858PaperGapConditionalCor312Actual
import tmp.sheaf.xif.paper.S881PaperGapIntrinsicVolumeS869Actual
import tmp.sheaf.xif.paper.S890CompatibilityScalingInstanceActual

-- S898: connect S890 qRoot/thetaHull paper log to S858 PaperGap.
-- The only exact field is P.signedHullLogVolume = thetaHullLog;
-- then PaperGap is filled using S881 intrinsic volume and S890/S864.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S898PaperGapFromScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S881PaperGapIntrinsicVolumeS869Actual
open LeanFormal.IUT.XiFPaper.S873PaperGapIntrinsicVolumeActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S890CompatibilityScalingInstanceActual
open LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual
open MeasureTheory

universe u uX uLabel

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)

theorem thetaHullLog_eq_neg_paperRoot :
    thetaHullLog (l := l) T b =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) := by
  rw [thetaHullLog_eq_qRootLog (l := l) T b]
  exact qRootLog_eq (l := l) T b

theorem thetaHullLog_eq_gapVolumeLog :
    thetaHullLog (l := l) T b =
      gapVolumeLog T b
        (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd) := by
  rw [thetaHullLog_eq_neg_paperRoot (l := l) T b]
  exact (gapRoot_value_eq (l := l) T b).symm

/-- Under the S881 exact hull field, the least-hull log equals thetaHullLog. -/
theorem leastHullLog_eq_thetaHullLog
    (h : S881HullLogExactGap (l := l) T b) :
    paperLeastLambdaOHullLog (l := l) T b Measure.addHaar =
      thetaHullLog (l := l) T b := by
  rw [h]
  exact (thetaHullLog_eq_gapVolumeLog (l := l) T b).symm

/-- Exact interface field: paper signed hull log equals the S890 theta hull log. -/
def S898SignedHullThetaInterface : Prop :=
  P.signedHullLogVolume = thetaHullLog (l := l) T b

/-- Fill S858 PaperGap from S890: signed log exact field plus S881 intrinsic. -/
noncomputable def paperGapFromScaling
    (hP : S898SignedHullThetaInterface (l := l) T b P)
    (hHull : S881HullLogExactGap (l := l) T b) :
    PaperGap (l := l) T b P where
  signed_hull_log_eq := by
    rw [hP, ← leastHullLog_eq_thetaHullLog (l := l) T b hHull]
  intrinsic := paperGapIntrinsicVolumeFromS869 (l := l) T b hHull

#check paperGapFromScaling
#check leastHullLog_eq_thetaHullLog
#check S898SignedHullThetaInterface

end LeanFormal.IUT.XiFPaper.S898PaperGapFromScalingActual

end