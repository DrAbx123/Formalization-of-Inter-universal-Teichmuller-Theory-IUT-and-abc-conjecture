/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import Mathlib.Tactic
/-! # Conditional refutation scheme for S45 from the donor power relation -/

The donor power relation (normalized = default^(1/d)) plus 1<d and default<1
implies qVFamNormRatio > 1, hence ratio != 1.  The donor relation is NOT proved
here; 1<d is also an explicit hypothesis.  This file records the exact
conditional refutation route, not an unconditional S45 refutation.
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0S45RefutationSchemeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
theorem qVFamDefaultNorm_lt_one :
    qVFamDefaultNorm T b < 1 := by
  unfold qVFamDefaultNorm
  exact qNorm_lt_one (qVFamily T b)
theorem qVFamDefaultNorm_pos : 0 < qVFamDefaultNorm T b := by
  unfold qVFamDefaultNorm
  exact qNorm_pos (qVFamily T b)
/-- Conditional refutation of ratio=1 from the donor power relation. -/
theorem qVFamNormRatio_ne_one_of_normalized_power
    (hpow : qVFamNormalizedNorm T b =
      (qVFamDefaultNorm T b) ^ (1 / (s1915LocalDegree T b : Real)))
    (hd : 1 < (s1915LocalDegree T b : Real)) :
    qVFamNormRatio T b ≠ 1 := by
  intro hratio
  have hdefpos : 0 < qVFamDefaultNorm T b := qVFamDefaultNorm_pos T b
  have hdeflt : qVFamDefaultNorm T b < 1 := qVFamDefaultNorm_lt_one T b
  have hdpos : (0 : Real) < (s1915LocalDegree T b : Real) := by linarith
  have hexp : 1 / (s1915LocalDegree T b : Real) < 1 :=
    (div_lt_one hdpos).mpr hd
  have hgt : qVFamDefaultNorm T b < qVFamNormalizedNorm T b := by
    rw [hpow]
    simpa using Real.rpow_lt_rpow_of_exponent_gt hdefpos hdeflt hexp
  have hratio_one : qVFamNormRatio T b = 1 := hratio
  unfold qVFamNormRatio at hratio_one
  have hlt : 1 < qVFamNormalizedNorm T b / qVFamDefaultNorm T b :=
    (one_lt_div hdefpos).mpr hgt
  linarith
end LeanFormal.IUT.XiFPaper.Mzk1P0S45RefutationSchemeActual
end