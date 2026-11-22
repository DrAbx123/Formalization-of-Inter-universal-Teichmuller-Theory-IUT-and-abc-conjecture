import tmp.sheaf.xif.paper.S809PaperLeastHullRootStackBridgeActual
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual

/-! # S817: norm of the finite root-stack unit

S809 asks for `StackRootUnitNormBridge` with paper norm
p^(-sum paperRootCoefficientFamily) = p^(-order/(2l)).  The actual stack root
unit is the image of `rootNormedUnit`; its norm is the S709 root norm
p^(-c_norm/(2l)), not p^(-order/(2l)) unless c_norm = order.  This file proves
the actual norm and the exact e_v factor between the two exponents.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S817StackRootUnitNormActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Actual norm of the stack root unit equals the root element norm. -/
theorem stackRootUnit_norm_eq_rootNormedElementNorm :
    ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ =
      rootNormedElementNorm (l := l) T b := by
  unfold stackRootUnit stackRootSection stackLUnitMap rootNormedUnit
  rfl

/-- Actual stack root norm: p^(-c_norm/(2l)), the S709 root radius formula. -/
theorem stackRootUnit_norm_eq_p_rpow :
    ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ =
      Real.rpow (qVFamTensorP T b : Real)
        (-(qVFamNormalizedCoefficient (l := l) T b) /
          (2 * (l.value : Real))) := by
  rw [stackRootUnit_norm_eq_rootNormedElementNorm]
  exact rootNormedElementNorm_eq_p_rpow (l := l) T b

/-- Exact e_v exponent difference between the actual spectral root norm and
the paper order/(2l) root norm. -/
noncomputable def stackRootNormExponentDifference : Real :=
  (qVFamNormalizedCoefficient (l := l) T b -
      ((qVFamily T b).order : Real)) / (2 * (l.value : Real))

/-- Paper target norm: p^(-order/(2l)). -/
noncomputable def stackRootUnitPaperNorm : Real :=
  Real.rpow (qVFamTensorP T b : Real)
    (-((qVFamily T b).order : Real) / (2 * (l.value : Real)))

/-- Exact factor form: actual stack-root norm = paper norm times the e_v
factor p^(-(c_norm - order)/(2l)). -/
theorem stackRootUnit_norm_eq_paperNorm_mul_exp_factor :
    ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ =
      stackRootUnitPaperNorm (l := l) T b *
        Real.rpow (qVFamTensorP T b : Real)
          (-(stackRootNormExponentDifference (l := l) T b)) := by
  rw [stackRootUnit_norm_eq_p_rpow]
  unfold stackRootUnitPaperNorm stackRootNormExponentDifference
  have hp : (0 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  have hle : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
  rw [show -(qVFamNormalizedCoefficient (l := l) T b) / (2 * (l.value : Real)) =
      -(((qVFamily T b).order : Real)) / (2 * (l.value : Real)) +
        (-((qVFamNormalizedCoefficient (l := l) T b - ((qVFamily T b).order : Real)) /
          (2 * (l.value : Real)))) by
    field_simp
    ring]
  exact Real.rpow_add hp _ _

/-- Exact bridge condition: the actual stack-root norm equals the paper norm
iff the spectral coefficient equals the paper order. -/
theorem stackRootUnit_norm_eq_paperNorm_iff :
    ‖(stackRootUnit (l := l) T b : rootStackExtension (l := l) T b)‖ =
        stackRootUnitPaperNorm (l := l) T b ↔
      qVFamNormalizedCoefficient (l := l) T b =
        ((qVFamily T b).order : Real) := by
  rw [stackRootUnit_norm_eq_p_rpow]
  unfold stackRootUnitPaperNorm
  have hp : (0 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  have hpne : (qVFamTensorP T b : Real) ≠ 1 := by
    have h1 : (1 : Real) < (qVFamTensorP T b : Real) :=
      by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
    linarith
  constructor
  · intro h
    have he := (Real.rpow_right_inj hp hpne).mp h
    have hl : (l.value : Real) ≠ 0 := by exact_mod_cast l.prime.ne_zero
    field_simp [hl] at he
    linarith
  · intro h
    rw [h]

end LeanFormal.IUT.XiFPaper.S817StackRootUnitNormActual

end
