/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic
/-! # Conditional norm bridge: default^(1/d) => ratio >= 1

The donor normalized-vs-default power relation is carried explicitly as `hbridge`;
this file proves the ratio >= 1 consequence without using S45. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.Mzk1GenericNormBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
theorem qVFamDefaultNorm_pos : 0 < qVFamDefaultNorm T b := by
  unfold qVFamDefaultNorm
  exact norm_pos_iff.mpr (qVFamily T b).q_ne_zero
theorem qVFamDefaultNorm_lt_one : qVFamDefaultNorm T b < 1 := by
  unfold qVFamDefaultNorm
  exact qNorm_lt_one (qVFamily T b)
/-- Conditional ratio >= 1 from the donor power relation. -/
theorem qVFamNormRatio_ge_one_of_norm_bridge
    (d : ℕ) (hd : 1 ≤ d)
    (hbridge : qVFamNormalizedNorm T b =
      (qVFamDefaultNorm T b) ^ (1 / (d : ℝ))) :
    1 ≤ qVFamNormRatio T b := by
  have hdefpos : 0 < qVFamDefaultNorm T b := qVFamDefaultNorm_pos T b
  have hdeflt : qVFamDefaultNorm T b < 1 := qVFamDefaultNorm_lt_one T b
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hexp : (1 : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdR]
    exact_mod_cast hd
  have hge : qVFamDefaultNorm T b ≤
      (qVFamDefaultNorm T b) ^ (1 / (d : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hdefpos (le_of_lt hdeflt) hexp
  have hnorm_ge : qVFamDefaultNorm T b ≤ qVFamNormalizedNorm T b := by
    rw [hbridge]
    exact hge
  unfold qVFamNormRatio
  exact (one_le_div hdefpos).mpr hnorm_ge
end LeanFormal.IUT.XiFPaper.Mzk1GenericNormBridgeActual
end