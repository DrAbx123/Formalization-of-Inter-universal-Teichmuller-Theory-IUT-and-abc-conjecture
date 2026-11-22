import tmp.sheaf.xif.paper.S817StackRootUnitNormActual
import tmp.sheaf.xif.paper.S820FiniteLScalingGeneratorActual
import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S809PaperLeastHullRootStackBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientOrderAuditActual

/-! # S826: c_norm = order iff e = 1

Task T gives the spectral coefficient `c_norm = order / e`, where `e` is the
relative ramification index e_v of the qVFamily F-place over its rational
prime.  This file records the exact iff and factor under the normalized norm
relation `||q|| = p^(-(order/e))`, and the S817 paper-norm bridge condition.
The actual ramification index computation remains the missing analytic norm
formula; no completion root is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual
open LeanFormal.IUT.XiFPaper.S817StackRootUnitNormActual
open LeanFormal.IUT.XiFPaper.S820FiniteLScalingGeneratorActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable (e : Real) (hepos : 0 < e)

/-- Task T's normalized norm relation, with e the relative ramification index. -/
def QVFamNormalizedNormCompatibility : Prop :=
  ‖qVFamNormalizedGenerator T b‖ =
    Real.rpow (qVFamTensorP T b : Real)
      (-(((qVFamily T b).order : Real) / e))

theorem qVFamNormalizedCoefficient_eq_order_div_e
    (h : QVFamNormalizedNormCompatibility (l := l) T b e) :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) / e := by
  unfold QVFamNormalizedNormCompatibility at h
  exact qVFamNormalizedCoefficient_eq_order_div_of_norm (l := l) T b e h

/-- Exact iff: c_norm = order exactly when e = 1. -/
theorem qVFamNormalizedCoefficient_eq_order_iff_e_eq_one
    (hepos : 0 < e)
    (h : QVFamNormalizedNormCompatibility (l := l) T b e) :
    qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) ↔ e = 1 := by
  rw [qVFamNormalizedCoefficient_eq_order_div_e (l := l) T b e h]
  have hopos : (0 : Real) < ((qVFamily T b).order : Real) :=
    by exact_mod_cast (qVFamily T b).order_pos
  have hene : e ≠ 0 := ne_of_gt hepos
  constructor
  · intro hEq
    have h' : ((qVFamily T b).order : Real) / e = ((qVFamily T b).order : Real) := hEq
    have hmul : ((qVFamily T b).order : Real) =
        ((qVFamily T b).order : Real) * e := (div_eq_iff hene).mp h'
    nlinarith
  · intro he
    rw [he]
    norm_num

/-- Exact factor: order - c_norm = order * (e - 1)/e. -/
theorem order_sub_qVFamNormalizedCoefficient_eq
    (hepos : 0 < e)
    (h : QVFamNormalizedNormCompatibility (l := l) T b e) :
    ((qVFamily T b).order : Real) - qVFamNormalizedCoefficient T b =
      ((qVFamily T b).order : Real) * ((e - 1) / e) := by
  rw [qVFamNormalizedCoefficient_eq_order_div_e (l := l) T b e h]
  field_simp [ne_of_gt hepos]

/-- If e ≠ 1, c_norm ≠ order. -/
theorem qVFamNormalizedCoefficient_ne_order_of_e_ne_one
    (hepos : 0 < e)
    (h : QVFamNormalizedNormCompatibility (l := l) T b e)
    (he : e ≠ 1) :
    qVFamNormalizedCoefficient T b ≠ ((qVFamily T b).order : Real) := by
  intro hcoe
  exact he ((qVFamNormalizedCoefficient_eq_order_iff_e_eq_one (l := l) T b e hepos h).mp hcoe)

/-- S817 paper-norm bridge for the stack root unit. -/
def StackRootPaperNormBridge : Prop :=
  ‖(LeanFormal.IUT.XiFPaper.S809PaperLeastHullRootStackBridgeActual.stackRootUnit (l := l) T b :
    rootStackExtension (l := l) T b)‖ =
    stackRootUnitPaperNorm (l := l) T b

theorem stackRootPaperNormBridge_iff_e_eq_one
    (hepos : 0 < e)
    (h : QVFamNormalizedNormCompatibility (l := l) T b e) :
    StackRootPaperNormBridge (l := l) T b ↔ e = 1 := by
  unfold StackRootPaperNormBridge
  rw [stackRootUnit_norm_eq_paperNorm_iff]
  exact qVFamNormalizedCoefficient_eq_order_iff_e_eq_one (l := l) T b e hepos h

/-- If e ≠ 1, the S809/S817 paper-norm bridge is false. -/
theorem StackRootPaperNormBridge_false_of_e_ne_one
    (hepos : 0 < e)
    (h : QVFamNormalizedNormCompatibility (l := l) T b e)
    (he : e ≠ 1) :
    ¬ StackRootPaperNormBridge (l := l) T b :=
  fun hb => he ((stackRootPaperNormBridge_iff_e_eq_one (l := l) T b e hepos h).mp hb)

/-- S820 finite-L factor-one condition; exact e = 1 condition, not an
unconditional construction. -/
def FiniteLScalingGeneratorFactorOneCondition : Prop :=
  StackRootUnitFactorOne (l := l) T b

end LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual

end
