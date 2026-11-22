import tmp.sheaf.xif.paper.S858PaperGapConditionalCor312Actual
import tmp.sheaf.xif.paper.S875PaperGapHullLogActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S884PaperGapIntrinsicVolumeRebuildActual

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
open LeanFormal.IUT.XiFPaper.S875PaperGapHullLogActual
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
    StackSectionCarrier (l := l) T b →* Multiplicative Real where
  toFun u := u.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Actual SourceLogShellDatum: K = Real, Units = StackSectionCarrier,
logMap = divisor coordinate, p = qVFamTensorP. -/
noncomputable def gapLogShellDatum : SourceLogShellDatum where
  p := qVFamTensorP T b
  hp := Fact.out
  K := Real
  Units := StackSectionCarrier (l := l) T b
  invariants := ⊤
  logMap := stackDivisorLogMap (l := l) T b

/-- Additive volume log V(x) = -x * log p. -/
noncomputable def gapVolumeLog : Real →+ Real where
  toFun x := -x * Real.log (qVFamTensorP T b : Real)
  map_zero' := by simp
  map_add' := by intro x y; ring

/-- Actual root unit: S782 stackRootSection. -/
noncomputable def gapRootUnit : (gapLogShellDatum (l := l) T b).Units :=
  stackRootSection (l := l) T b

/-- Actual root normalization V(root) = -(order/(2l))*log p. -/
theorem gapRoot_value_eq :
    gapVolumeLog (l := l) T b
        (((gapLogShellDatum (l := l) T b).logMap
          (gapRootUnit (l := l) T b)).toAdd) =
      -((((qVFamily T b).order : Real) / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) := by
  unfold gapVolumeLog gapRootUnit gapLogShellDatum stackDivisorLogMap
  change -((stackRootSection (l := l) T b).2.toAdd) *
      Real.log (qVFamTensorP T b : Real) =
    -(((qVFamily T b).order : Real) / (2 * (l.value : Real)) *
      Real.log (qVFamTensorP T b : Real))
  rw [stackRootSection]
  simp

/-- Full PaperGapIntrinsicVolume from the exact scaling data at cRoot. -/
noncomputable def paperGapIntrinsicVolumeOfData
    (data : ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b)) :
    PaperGapIntrinsicVolume (l := l) T b where
  D := gapLogShellDatum (l := l) T b
  rootUnit := gapRootUnit (l := l) T b
  volumeLog := gapVolumeLog (l := l) T b
  root_value_eq := gapRoot_value_eq (l := l) T b
  hull_log_eq_root := by
    rw [paperLeastLambdaOHullLog_eq_neg_order_div (l := l) T b data]
    exact (gapRoot_value_eq (l := l) T b).symm

/-- Exact single field: the cRoot scaling datum. -/
def PaperGapIntrinsicVolumeExactField : Prop :=
  Nonempty (ArithmeticTuplePureFractionalScalingData
    (qVFamTensorPlaces T b) qVFamTensorTuple (paperRootCoefficientFamily (l := l) T b))

/-- Conditional full intrinsic volume inhabitant from the exact field. -/
theorem paperGapIntrinsicVolume_nonempty_of_field
    (h : PaperGapIntrinsicVolumeExactField (l := l) T b) :
    Nonempty (PaperGapIntrinsicVolume.{0} (l := l) T b) := by
  rcases h with ⟨data⟩
  exact ⟨paperGapIntrinsicVolumeOfData (l := l) T b data⟩

end LeanFormal.IUT.XiFPaper.S884PaperGapIntrinsicVolumeRebuildActual

end
