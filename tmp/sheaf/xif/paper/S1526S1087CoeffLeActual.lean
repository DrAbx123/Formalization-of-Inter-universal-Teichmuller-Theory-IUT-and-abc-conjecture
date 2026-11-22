import tmp.sheaf.xif.paper.S1087Q1UContainmentActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientOrderAuditActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1526S1087CoeffLeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual
open LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact first missing number-theory lemma: the residue norm base at the
actual F-place is at least the rational prime, equivalently the base-residue
log ratio is at least one. -/
def S1526ResidueLogRatioGeOne : Prop :=
  1 ≤ Real.log (residueNormBase (qVFamTensorPlace T b)) /
    Real.log (qVFamTensorP T b : Real)

/-- The pure qVFam coefficient is the default completion coefficient. -/
theorem s1526PureCoefficient_eq_default :
    qVFamPureCoefficient T b () = qVFamDefaultCoefficient T b := rfl

/-- Exact coefficient comparison follows from the residue log-ratio bound. -/
theorem s1526CoeffLe_of_residueLogRatio
    (h : S1526ResidueLogRatioGeOne (l := l) T b) :
    S1087CoeffLe (l := l) T b := by
  unfold S1087CoeffLe
  intro i
  cases i
  unfold paperRootCoefficientFamily
  change qVFamPaperRootCoefficient T b ≤ qVFamPureCoefficient T b ()
  have hdefault := qVFamDefaultCoefficient_eq_order_mul (l := l) T b
  have hpure : qVFamPureCoefficient T b () = qVFamDefaultCoefficient T b := rfl
  rw [hpure, hdefault]
  have horder : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
  have hratio := h
  have hle_mul : ((qVFamily T b).order : Real) ≤
      ((qVFamily T b).order : Real) *
        (Real.log (residueNormBase (qVFamTensorPlace (l := l) T b)) /
          Real.log (qVFamTensorP (l := l) T b : Real)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio horder
  have hroot_le_order := qVFamPaperRootCoefficient_le_normalized (l := l) T b
  unfold qVFamNormalizedCoefficient at hroot_le_order
  exact hroot_le_order.trans hle_mul

/-- The coefficient comparison is exactly the consumer of the residue log-ratio
number theory lemma. -/
def S1526ExactFirstNumberTheoryLemma : Prop :=
  S1526ResidueLogRatioGeOne (l := l) T b

end LeanFormal.IUT.XiFPaper.S1526S1087CoeffLeActual

end
