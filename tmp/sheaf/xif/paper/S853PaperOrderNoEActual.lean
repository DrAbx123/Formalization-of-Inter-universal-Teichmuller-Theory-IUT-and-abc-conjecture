import tmp.sheaf.xif.paper.S817StackRootUnitNormActual
import tmp.sheaf.xif.paper.S850LocalQParameterNormalizationActual
import tmp.sheaf.xif.paper.S795OrderSemanticsActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S809PaperLeastHullRootStackBridgeActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S853PaperOrderNoEActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual
open LeanFormal.IUT.XiFPaper.S817StackRootUnitNormActual
open LeanFormal.IUT.XiFPaper.S795OrderSemanticsActual
open LeanFormal.IUT.XiFPaper.S850LocalQParameterNormalizationActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Correct paper root coefficient: order/(2l), no e factor. -/
theorem paperRootCoefficientFamily_eq_order_div :
    paperRootCoefficientFamily T b =
      fun _ => ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
  funext i
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient
  rfl

theorem paperRootCoefficientFamily_no_e (i : qVFamTensorV) :
    paperRootCoefficientFamily T b i =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
  rw [paperRootCoefficientFamily_eq_order_div]

/-- Correct paper normalization branch: order = Lean exponent (pi_v uniformizer). -/
theorem qVFamily_order_eq_lean_exponent :
    (qVFamily T b).order = Int.toNat (qVFamily T b).exponent :=
  qVFamily_order_eq_valuation (l := l) T b

/-- The real e_v obstacle: the actual stack root norm differs from the paper
order/(2l) norm by the spectral-vs-order factor. -/
def StackRootNormEVMismatch : Prop :=
  ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ ≠
    stackRootUnitPaperNorm (l := l) T b

theorem stackRootNormEVMismatch_iff :
    StackRootNormEVMismatch T b ↔
      qVFamNormalizedCoefficient T b ≠ ((qVFamily T b).order : Real) := by
  unfold StackRootNormEVMismatch
  constructor
  · intro h heq
    exact h ((stackRootUnit_norm_eq_paperNorm_iff (l := l) T b).mpr heq)
  · intro h hnorm
    exact h ((stackRootUnit_norm_eq_paperNorm_iff (l := l) T b).mp hnorm)

theorem stackRootUnit_norm_eq_paper_mul_factor :
    ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ =
      stackRootUnitPaperNorm (l := l) T b *
        Real.rpow (qVFamTensorP T b : Real)
          (-(stackRootNormExponentDifference (l := l) T b)) :=
  stackRootUnit_norm_eq_paperNorm_mul_exp_factor (l := l) T b

end LeanFormal.IUT.XiFPaper.S853PaperOrderNoEActual
end