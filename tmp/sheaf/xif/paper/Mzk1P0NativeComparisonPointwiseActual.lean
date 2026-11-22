/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
import tmp.sheaf.xif.paper.Mzk1P0NativeReadoutActual
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import Mathlib.Tactic
/-! #1: R3.7 blockwise native identification implies pointwise native comparison -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonPointwiseActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P3MassIdentificationActual
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
theorem nativeQReadout_le_thetaReadout_of_R37
    (h : R37R13NativeMassIdentification T b) :
    nativeQReadout T b ≤ nativeThetaReadout T b := by
  have hcoeff := (R37R13NativeMassIdentification_iff_coefficient T b).mp h
  have hlog : Real.log ‖p2Coefficient T b‖ ≤ 0 :=
    Real.log_nonpos (le_of_lt (norm_pos_iff.mpr (p2Coeff_ne_zero T b)))
      (p2Coefficient_norm_le_one T b)
  linarith
theorem nativePointwiseComparison_of_blockwise_R37
    (h : ∀ b : Bad (nativePlaceSelection T), R37R13NativeMassIdentification T b) :
    ∀ b : Bad (nativePlaceSelection T),
      nativeQReadout T b ≤ nativeThetaReadout T b := fun b =>
  nativeQReadout_le_thetaReadout_of_R37 T b (h b)
end LeanFormal.IUT.XiFPaper.Mzk1P0NativeComparisonPointwiseActual
end
