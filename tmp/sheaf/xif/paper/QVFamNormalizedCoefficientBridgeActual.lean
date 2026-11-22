import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# Bridge from the normalized qVFamily coefficient to local log magnitude

For the actual qVFamily q, the normalized spectral coefficient is

  c_norm = -logb_p ||q||_normalized.

The classical q-pilot local log magnitude uses the default completion valuation
norm:

  localLogMagnitude q = -log ||q||_default.

This file proves the exact factor relation

  c_norm * log p = localLogMagnitude q - log (||q||_normalized / ||q||_default)

and its conditional equality form when the two norm instances agree.  The
ratio is the exact object-level normalization factor; no norm-instance equality
is asserted unless supplied.

No sorry/axiom/True/PUnit, no inequality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The normalized spectral norm of the qVFamily q. -/
noncomputable def qVFamNormalizedNorm : Real :=
  ‖qVFamNormalizedGenerator T b‖

/-- The default valuation norm of the qVFamily q. -/
noncomputable def qVFamDefaultNorm : Real :=
  ‖(qVFamily T b).q‖

/-- The exact ratio of the normalized spectral norm to the default valuation
norm on the same actual qVFamily element. -/
noncomputable def qVFamNormRatio : Real :=
  qVFamNormalizedNorm T b / qVFamDefaultNorm T b

/-- Exact object-level norm-instance equality for qVFamily. -/
def QVFamNormInstanceGap : Prop :=
  qVFamNormalizedNorm T b = qVFamDefaultNorm T b

/-- The normalized coefficient times log p is the negative normalized log norm. -/
theorem qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
      -Real.log (qVFamNormalizedNorm T b) := by
  have hprime : Nat.Prime (qVFamTensorP T b) :=
    Fact.out (p := Nat.Prime (qVFamTensorP T b))
  have hp1 : (1 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast hprime.one_lt
  have hp0 : (0 : Real) < (qVFamTensorP T b : Real) :=
    lt_trans zero_lt_one hp1
  have hpne : (qVFamTensorP T b : Real) ≠ 1 := ne_of_gt hp1
  have hlogne : Real.log (qVFamTensorP T b : Real) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp0 hpne
  have hnormne : qVFamNormalizedNorm T b ≠ 0 := by
    unfold qVFamNormalizedNorm
    exact norm_ne_zero_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)
  unfold qVFamNormalizedCoefficient qVFamNormalizedNorm
  rw [Real.logb]
  field_simp [hlogne, hnormne]

/-- The classical local log magnitude is the negative default-norm log. -/
theorem localLogMagnitude_qVFamily_eq :
    localLogMagnitude (qVFamily T b) =
      -Real.log (qVFamDefaultNorm T b) := by
  unfold localLogMagnitude localSignedLog qVFamDefaultNorm
  rfl

/-- Exact factor relation: the normalized coefficient differs from the
classical local log magnitude by the normalized/default norm ratio. -/
theorem qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
      localLogMagnitude (qVFamily T b) - Real.log (qVFamNormRatio T b) := by
  have hnormne : qVFamNormalizedNorm T b ≠ 0 := by
    unfold qVFamNormalizedNorm
    exact norm_ne_zero_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)
  have hdefne : qVFamDefaultNorm T b ≠ 0 := by
    unfold qVFamDefaultNorm
    exact norm_ne_zero_iff.mpr (qVFamily T b).q_ne_zero
  rw [qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm,
    localLogMagnitude_qVFamily_eq]
  unfold qVFamNormRatio
  rw [Real.log_div hnormne hdefne]
  ring

/-- Exact order/residueNorm formula for the normalized coefficient.  The
normalized spectral coefficient times log p is the actual qVFamily order times
the F-place residue-norm logarithm, minus the normalized/default norm-ratio
logarithm.  This uses the actual qVFamily order/residueNorm and the actual
normalized norm; no norm-instance equality is assumed. -/
theorem qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
      ((qVFamily T b).order : Real) *
          Real.log (residueNormBase (qVFamTensorPlace T b)) -
        Real.log (qVFamNormRatio T b) := by
  rw [qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio]
  rw [localLogMagnitude_eq_order_mul_log (parameter := qVFamily T b)]

/-- The same order/residueNorm formula through the actual tensor coefficient. -/
theorem qVFamNormalizedCoefficient_mul_log_eq_tensorCoefficient_mul_log_residueNormBase_sub_log_ratio :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
      qVFamTensorCoefficient T b *
          Real.log (residueNormBase (qVFamTensorPlace T b)) -
        Real.log (qVFamNormRatio T b) := by
  rw [qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio]
  unfold qVFamTensorCoefficient
  rfl

/-- Conditional equality with the classical local log magnitude, exactly when
the two norm instances agree on the qVFamily element. -/
theorem qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_of_norm_eq
    (h : QVFamNormInstanceGap T b) :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
      localLogMagnitude (qVFamily T b) := by
  have hratio : qVFamNormRatio T b = 1 := by
    unfold qVFamNormRatio
    rw [h]
    exact div_self (by
      unfold qVFamDefaultNorm
      exact norm_ne_zero_iff.mpr (qVFamily T b).q_ne_zero)
  rw [qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio,
    hratio, Real.log_one, sub_zero]

/-- Equivalence: the classical bridge holds iff the two norm instances agree. -/
theorem qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_iff :
    qVFamNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real) =
        localLogMagnitude (qVFamily T b) ↔
      QVFamNormInstanceGap T b := by
  constructor
  · intro h
    have hfactor :=
      qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_sub_log_ratio T b
    have hratio : Real.log (qVFamNormRatio T b) = 0 := by
      linarith
    have hratio_pos : 0 < qVFamNormRatio T b := by
      unfold qVFamNormRatio
      exact div_pos
        (by
          unfold qVFamNormalizedNorm
          exact norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b))
        (by
          unfold qVFamDefaultNorm
          exact norm_pos_iff.mpr (qVFamily T b).q_ne_zero)
    have hratio_one : qVFamNormRatio T b = 1 := by
      exact Real.eq_one_of_pos_of_log_eq_zero hratio_pos hratio
    unfold QVFamNormInstanceGap
    have hdefne : qVFamDefaultNorm T b ≠ 0 := by
      unfold qVFamDefaultNorm
      exact norm_ne_zero_iff.mpr (qVFamily T b).q_ne_zero
    unfold qVFamNormRatio at hratio_one
    rw [div_eq_iff hdefne] at hratio_one
    simpa using hratio_one
  · exact qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_of_norm_eq T b



/-- The normalized norm projection. -/
theorem qVFamNormalizedNorm_eq :
    qVFamNormalizedNorm T b = ‖qVFamNormalizedGenerator T b‖ := rfl

/-- The default norm projection. -/
theorem qVFamDefaultNorm_eq :
    qVFamDefaultNorm T b = ‖(qVFamily T b).q‖ := rfl

end LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
