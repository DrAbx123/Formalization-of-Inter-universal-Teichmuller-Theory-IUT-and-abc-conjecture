-- INVALID: S875 audit found this file does not compile (rfl / paperRootCoefficientFamily unknown).
-- Do not queue/use. Use S875PaperGapHullLogActual instead.
import tmp.sheaf.xif.paper.S858PaperGapConditionalCor312Actual
import tmp.sheaf.xif.paper.S822PadicDetHullActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.Algebra.Group.TypeTags.Basic

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S873PaperGapIntrinsicVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S822PadicDetHullActual
open LeanFormal.IUT.XiFPaper.S858PaperGapConditionalCor312Actual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Divisor-coordinate monoid hom on S782 stack sections. -/
noncomputable def stackDivisorLogMap :
    StackSectionCarrier T b →* Multiplicative Real where
  toFun u := u.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Actual SourceLogShellDatum: K = Real, Units = StackSectionCarrier,
logMap = divisor coordinate, p = qVFamTensorP. -/
noncomputable def gapLogShellDatum : SourceLogShellDatum where
  p := qVFamTensorP T b
  hp := Fact.out
  K := Real
  Units := StackSectionCarrier T b
  invariants := ⊤
  logMap := stackDivisorLogMap T b

/-- Additive volume log V(x) = -x * log p. -/
noncomputable def gapVolumeLog : Real →+ Real where
  toFun x := -x * Real.log (qVFamTensorP T b : Real)
  map_zero' := by simp
  map_add' := by intro x y; ring

/-- Actual root unit: S782 stackRootSection. -/
noncomputable def gapRootUnit : (gapLogShellDatum T b).Units :=
  stackRootSection (l := l) T b

/-- Actual root normalization V(root) = -(order/(2l))*log p. -/
theorem gapRoot_value_eq :
    gapVolumeLog T b
        (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd) =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold gapVolumeLog gapRootUnit gapLogShellDatum stackDivisorLogMap
  change -((stackRootSection (l := l) T b).2.toAdd) *
      Real.log (qVFamTensorP T b : Real) =
    -(((qVFamily T b).order : Real) / (2 * (l.value : Real)) *
      Real.log (qVFamTensorP T b : Real))
  rw [stackRootSection]
  simp

/-- Single exact field: least-hull log equals the actual intrinsic root volume. -/
def S873HullLogExactGap : Prop :=
  paperLeastLambdaOHullLog (l := l) T b Measure.addHaar =
    gapVolumeLog T b
      (((gapLogShellDatum T b).logMap (gapRootUnit (l := l) T b)).toAdd)

/-- Actual PaperGapIntrinsicVolume from the single exact hull-log field. -/
noncomputable def paperGapIntrinsicVolumeOfHullLogEq
    (h : S873HullLogExactGap (l := l) T b) :
    PaperGapIntrinsicVolume (l := l) T b where
  D := gapLogShellDatum T b
  rootUnit := gapRootUnit (l := l) T b
  volumeLog := gapVolumeLog T b
  root_value_eq := gapRoot_value_eq (l := l) T b
  hull_log_eq_root := h

/-- Conditional proof of the single hull-log field from actual scaling data. -/
theorem s873HullLogExactGap_of_data
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b)) :
    S873HullLogExactGap (l := l) T b := by
  unfold S873HullLogExactGap
  rw [paperLeastLambdaOHullLog_eq_formula (l := l) T b Measure.addHaar data]
  have hsum : (∑ i : qVFamTensorV, paperRootCoefficientFamily T b i) =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
    simp [paperRootCoefficientFamily, qVFamPaperRootCoefficient, Finset.sum_const,
      qVFamTensorV, nsmul_eq_mul]
  rw [hsum]
  unfold gapVolumeLog gapLogShellDatum gapRootUnit stackDivisorLogMap stackRootSection
  simp

/-- Fully actual intrinsic volume conditional only on the exact hull-log field. -/
noncomputable def paperGapIntrinsicVolume_of_data
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b)) :
    PaperGapIntrinsicVolume (l := l) T b :=
  paperGapIntrinsicVolumeOfHullLogEq (l := l) T b
    (s873HullLogExactGap_of_data (l := l) T b data)

end LeanFormal.IUT.XiFPaper.S873PaperGapIntrinsicVolumeActual

end
