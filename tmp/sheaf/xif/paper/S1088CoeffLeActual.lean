import tmp.sheaf.xif.paper.S1087Q1UContainmentActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientOrderAuditActual
/-! # S1088: S1087CoeffLe from the default coefficient formula
qVFamPureCoefficient = qVFamDefaultCoefficient = order * (log residue / log p).
With order >= 1 and log residue / log p >= 1, this is >= order >= order/(2l). -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1088CoeffLeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual
open LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
theorem qVFamPureCoefficient_eq_default :
    qVFamPureCoefficient T b () = qVFamDefaultCoefficient (l := l) T b := rfl
/-- Exact residue-degree input: log(residue)/log(p) >= 1. -/
def S1088RatioGeOne : Prop :=
    1 ≤ Real.log (residueNormBase (qVFamTensorPlace T b)) /
      Real.log (qVFamTensorP T b : Real)
theorem qVFamPureCoefficient_ge_order
    (hres : S1088RatioGeOne (l := l) T b) :
    ((qVFamily T b).order : Real) ≤ qVFamPureCoefficient T b () := by
  have horder : (1 : Real) ≤ ((qVFamily T b).order : Real) := by
    exact_mod_cast Nat.succ_le_of_lt (qVFamily T b).order_pos
  have hcoef : qVFamPureCoefficient T b () =
      ((qVFamily T b).order : Real) *
        (Real.log (residueNormBase (qVFamTensorPlace T b)) /
          Real.log (qVFamTensorP T b : Real)) := by
    rw [qVFamPureCoefficient_eq_default (l := l) T b]
    rw [qVFamDefaultCoefficient_eq_order_mul (l := l) T b]
  rw [hcoef]
  unfold S1088RatioGeOne at hres
  have hordernonneg : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
  nlinarith [horder, hres]
theorem s1087CoeffLe_actual
    (hres : S1088RatioGeOne (l := l) T b) :
    S1087CoeffLe (l := l) T b := by
  intro i
  have horder : (1 : Real) ≤ ((qVFamily T b).order : Real) := by
    exact_mod_cast Nat.succ_le_of_lt (qVFamily T b).order_pos
  have hden : (1 : Real) ≤ 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    nlinarith
  have hc := qVFamPureCoefficient_ge_order (l := l) T b hres
  have hroot : paperRootCoefficientFamily (l := l) T b i =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
    unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
    rfl
  rw [hroot]
  have hordernonneg : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
  calc
    ((qVFamily T b).order : Real) / (2 * (l.value : Real)) ≤
        ((qVFamily T b).order : Real) / 1 := by
      exact div_le_div_of_nonneg_left hordernonneg (by norm_num) hden
    _ = ((qVFamily T b).order : Real) := div_one _
    _ ≤ qVFamPureCoefficient T b () := hc
end LeanFormal.IUT.XiFPaper.S1088CoeffLeActual
