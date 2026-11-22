import tmp.sheaf.xif.paper.S873PaperGapIntrinsicVolumeActual
import tmp.sheaf.xif.paper.S864PaperLambdaOLogVolumeActual
import tmp.sheaf.xif.paper.S872OtriLogVolumeInterfaceActual
import tmp.sheaf.xif.paper.S859PaperIntrinsicLogVolumeActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S883HullLogSingleFieldActual

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
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S859PaperIntrinsicLogVolumeActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S864PaperLambdaOLogVolumeActual
open LeanFormal.IUT.XiFPaper.S872OtriLogVolumeInterfaceActual
open LeanFormal.IUT.XiFPaper.S873PaperGapIntrinsicVolumeActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Actual sign relation: the lambda-O log-volume at cRoot equals the actual
root intrinsic volume. -/
theorem lambdaOLogVolume_eq_gapVolumeLog :
    paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) =
      gapVolumeLog T b
        (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd) := by
  rw [paperLambdaOLogVolume_cRoot_eq_neg_section (l := l) T b]
  rw [paperIntrinsicLogVolume_root (l := l) T b]
  rw [gapRoot_value_eq (l := l) T b]

/-- The single exact field is equivalent to the S864 V_lambdaO formulation. -/
theorem s883HullLogExactGap_iff_lambdaO :
    S873HullLogExactGap (l := l) T b ↔
      paperLeastLambdaOHullLog T b Measure.addHaar =
        paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) := by
  unfold S873HullLogExactGap
  constructor
  · intro h
    rw [lambdaOLogVolume_eq_gapVolumeLog (l := l) T b]
    exact h
  · intro h
    rw [lambdaOLogVolume_eq_gapVolumeLog (l := l) T b] at h
    exact h

/-- Interface-valued alternative definition, using S872 V_lambdaO on the least
hull.  This is explicitly an interface, not the actual Haar log. -/
noncomputable def paperLeastLambdaOHullLogInterface : Real :=
  paperLogVolumeOnHull (l := l) T b (paperLeastLambdaOHull (l := l) T b)

theorem paperLeastLambdaOHullLogInterface_eq_lambdaO :
    paperLeastLambdaOHullLogInterface (l := l) T b =
      paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b) :=
  paperLogVolumeOnHull_least (l := l) T b

structure S883HullLogInterface where
  value : Real
  value_eq_lambdaO :
    value = paperLambdaOLogVolume (l := l) T b (paperRootCoefficientFamily T b)

noncomputable def s883HullLogInterface : S883HullLogInterface (l := l) T b where
  value := paperLeastLambdaOHullLogInterface (l := l) T b
  value_eq_lambdaO := paperLeastLambdaOHullLogInterface_eq_lambdaO (l := l) T b

theorem paperLeastLambdaOHullLogInterface_eq_gapVolume :
    paperLeastLambdaOHullLogInterface (l := l) T b =
      gapVolumeLog T b
        (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd) := by
  rw [paperLeastLambdaOHullLogInterface_eq_lambdaO (l := l) T b]
  exact lambdaOLogVolume_eq_gapVolumeLog (l := l) T b

/-- Exact minimal datum: pure fractional scaling data at cRoot. -/
def S883ScalingDataRequired : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple
    (paperRootCoefficientFamily T b))

/-- Conditional actual single-field proof from the minimal scaling datum. -/
theorem s883HullLogExactGap_of_scalingData
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b)) :
    S873HullLogExactGap (l := l) T b :=
  s873HullLogExactGap_of_data (l := l) T b data

/-- The actual single field is still the open condition; interface value is
not substituted for it. -/
def S883ActualHullLogStillOpen : Prop :=
  S873HullLogExactGap (l := l) T b

end LeanFormal.IUT.XiFPaper.S883HullLogSingleFieldActual

end
