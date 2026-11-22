/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import Mathlib.Tactic

/-! # S45 norm-ratio realization (honest form)

`qVFamNormRatio = qVFamNormalizedNorm / qVFamDefaultNorm` is the ratio of the normalized
(spectral) norm to the default (valued-adic) norm of the same qVFamily element.
The paper S45 condition `qVFamNormRatio = 1` is therefore EXACTLY the explicit
norm-instance equality `QVFamNormInstanceGap`; it is not implied by the donor power
formula and is kept as an explicit condition (no fake). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1S45NormRatioRealizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

theorem qVFamDefaultNorm_ne_zero : qVFamDefaultNorm T b ≠ 0 := by
  unfold qVFamDefaultNorm
  exact norm_ne_zero_iff.mpr (qVFamily T b).q_ne_zero

theorem qVFamDefaultNorm_pos : 0 < qVFamDefaultNorm T b := by
  unfold qVFamDefaultNorm
  exact norm_pos_iff.mpr (qVFamily T b).q_ne_zero

theorem qVFamNormalizedNorm_ne_zero : qVFamNormalizedNorm T b ≠ 0 := by
  unfold qVFamNormalizedNorm
  exact norm_ne_zero_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)

theorem qVFamNormalizedNorm_pos : 0 < qVFamNormalizedNorm T b := by
  unfold qVFamNormalizedNorm
  exact norm_pos_iff.mpr (qVFamNormalizedGenerator_ne_zero T b)

/-- Multiplicative form: the ratio times the default norm is the normalized norm. -/
theorem qVFamNormRatio_mul_default :
    qVFamNormRatio T b * qVFamDefaultNorm T b = qVFamNormalizedNorm T b := by
  unfold qVFamNormRatio
  rw [div_mul_cancel₀ _ (qVFamDefaultNorm_ne_zero T b)]

/-- **S45 realization, honest form**: the paper condition is exactly the explicit
norm-instance equality, not a consequence of the power formula. -/
theorem qVFamNormRatio_eq_one_iff_gap :
    qVFamNormRatio T b = 1 ↔ QVFamNormInstanceGap T b := by
  unfold qVFamNormRatio QVFamNormInstanceGap
  exact div_eq_one_iff_eq (qVFamDefaultNorm_ne_zero T b)

theorem qVFamNormRatio_pos : 0 < qVFamNormRatio T b := by
  unfold qVFamNormRatio
  exact div_pos (qVFamNormalizedNorm_pos T b) (qVFamDefaultNorm_pos T b)

theorem qVFamNormRatio_ne_one_of_gap_false
    (h : ¬ QVFamNormInstanceGap T b) : qVFamNormRatio T b ≠ 1 := by
  intro h1
  exact h ((qVFamNormRatio_eq_one_iff_gap T b).mp h1)

def s45NormRatioRows : List (String × String × String) :=
  [ ("qVFamNormRatio_eq_one_iff_gap", "S45 ratio=1 <=> explicit norm-instance equality QVFamNormInstanceGap", "PROVED"),
    ("qVFamNormRatio_mul_default", "ratio * default norm = normalized norm", "PROVED"),
    ("qVFamNormRatio_pos", "ratio positive (norms nonzero)", "PROVED"),
    ("qVFamNormRatio_ne_one_of_gap_false", "gap false => ratio ne 1", "PROVED"),
    ("QVFamNormInstanceGap", "explicit norm-instance equality (S45 source condition)", "EXPLICIT CONDITION") ]

theorem s45NormRatioRows_length : s45NormRatioRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S45NormRatioRealizationActual

end