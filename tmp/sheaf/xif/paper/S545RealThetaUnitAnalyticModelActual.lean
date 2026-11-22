import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceThetaDivisor
import tmp.sheaf.xif.paper.S543ConditionalEtThRecipeActual

-- S545: old Example 3.6 thetaUnit/thetaQUnit/thetaRootValue are real
-- analytic units.  Construct real thetaLabel/qHalf powers and mu2l action;
-- bridge to the nonarchimedean ACF thetaUnit remains exact.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S545RealThetaUnitAnalyticModelActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S543ConditionalEtThRecipeActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaDivisor
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceThetaGenerator
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (t : AnalyticThetaCarrier)

-- Label powers in the real analytic model.
noncomputable def realThetaLabelUnit (t : AnalyticThetaCarrier) (j : ℤ) : ℝˣ :=
  thetaUnit t j

theorem realThetaLabelUnit_eq_qUnit_pow (j : ℤ) :
    realThetaLabelUnit t j = thetaQUnit t ^ (gaussExponent j).toNat :=
  thetaUnit_eq_qUnit_pow t j

-- Given a supplied real 2l-th root r of q, produce qHalf = r^l.
noncomputable def realQHalfUnit (r : ℝ) (hr : r ^ (2 * l.value) = t.q) : ℝˣ :=
  Units.mk0 (r ^ l.value) (by
    apply pow_ne_zero
    intro hzero
    have hpow := hr
    rw [hzero, zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow
    have hqpos := t.q_pos
    linarith)

theorem realQHalfUnit_sq (r : ℝ) (hr : r ^ (2 * l.value) = t.q) :
    realQHalfUnit (l := l) t r hr ^ 2 = thetaQUnit t := by
  ext
  simp only [realQHalfUnit, Units.val_pow_eq_pow_val, Units.val_mk0, thetaQUnit_apply]
  rw [← pow_mul, show l.value * 2 = 2 * l.value by ring, hr]

-- Actual mu2l action on the real root theta values (supplied root/unity).
theorem realRootMu2lAction (ζ r : ℝ) (hζ : ζ ^ (2 * l.value) = 1) (j : ℤ) :
    thetaRootValue (ζ * r) j = (ζ ^ (gaussExponent j).toNat) * thetaRootValue r j ∧
      (ζ ^ (gaussExponent j).toNat) ^ (2 * l.value) = 1 :=
  thetaRootValue_mul_root_of_pow_eq_one ζ r l.value hζ j

-- Exact missing bridge: real analytic units -> nonarchimedean ACF theta units.
structure RealToNonarchimedeanThetaBridgeGap where
  realUnit : ℝˣ
  nonarchUnit : (ACF T b)ˣ
  unitMap : ℝˣ → (ACF T b)ˣ
  qHalf_compat : Prop
  thetaLabel_compat : Prop
  mu2l_compat : Prop

#check realThetaLabelUnit
#check realThetaLabelUnit_eq_qUnit_pow
#check realQHalfUnit_sq
#check realRootMu2lAction
#check RealToNonarchimedeanThetaBridgeGap

end LeanFormal.IUT.XiFPaper.S545RealThetaUnitAnalyticModelActual

end