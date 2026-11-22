import tmp.sheaf.xif.paper.S873PaperGapIntrinsicVolumeActual
import tmp.sheaf.xif.paper.S869OtriGapsFilledActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual

-- S881: S858 PaperGapIntrinsicVolume from S873 actual datum and S869
-- divisor*log p measure; hull_log_eq_root is the exact single field.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S881PaperGapIntrinsicVolumeS869Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S873PaperGapIntrinsicVolumeActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S869OtriGapsFilledActual
open LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The single exact hull-log field: least-hull log equals intrinsic root volume. -/
def S881HullLogExactGap : Prop :=
  paperLeastLambdaOHullLog (l := l) T b Measure.addHaar =
    gapVolumeLog T b
      (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd)

theorem S881HullLogExactGap_eq_S873 :
    S881HullLogExactGap (l := l) T b ↔ S873HullLogExactGap (l := l) T b :=
  Iff.rfl

/-- Actual PaperGapIntrinsicVolume using S873 D/rootUnit/volumeLog and
S869's divisor*log p root value, conditional on the exact hull field. -/
noncomputable def paperGapIntrinsicVolumeFromS869
    (h : S881HullLogExactGap (l := l) T b) :
    PaperGapIntrinsicVolume (l := l) T b where
  D := gapLogShellDatum T b
  rootUnit := gapRootUnit (l := l) T b
  volumeLog := gapVolumeLog T b
  root_value_eq := gapRoot_value_eq (l := l) T b
  hull_log_eq_root := h

/-- The same root value is the negative of S869's nonunit divisor*log p measure. -/
theorem root_value_eq_neg_S869_measure :
    gapVolumeLog T b
        (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd) =
      -otriNonunitLogMeasure (l := l) T b (stackRootSection (l := l) T b) := by
  rw [gapRoot_value_eq (l := l) T b,
    otriNonunitLogMeasure_root (l := l) T b]

/-- Fully actual fields, with only the single exact hull-log field remaining. -/
noncomputable def paperGapIntrinsicVolumeFromS869OfData
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b)) :
    PaperGapIntrinsicVolume (l := l) T b :=
  paperGapIntrinsicVolumeFromS869 (l := l) T b
    ((S881HullLogExactGap_eq_S873 (l := l) T b).mpr
      (s873HullLogExactGap_of_data (l := l) T b data))

#check paperGapIntrinsicVolumeFromS869
#check root_value_eq_neg_S869_measure
#check paperGapIntrinsicVolumeFromS869OfData

end LeanFormal.IUT.XiFPaper.S881PaperGapIntrinsicVolumeS869Actual

end