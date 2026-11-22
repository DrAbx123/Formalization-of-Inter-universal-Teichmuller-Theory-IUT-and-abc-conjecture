/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S709RootImageRadiusFormulaActual
import tmp.sheaf.xif.paper.S305SingleLambdaNormActual
import tmp.sheaf.xif.paper.Mzk1A1SignedReadoutProductActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic

/-! # P1 #1: exact theta-root / log-radius dictionary (S201 + S709 green donors). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1RootRadiusBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.S201RootThetaNormLActual
open LeanFormal.IUT.XiFPaper.S709RootImageRadiusFormulaActual
open LeanFormal.IUT.XiFPaper.S305SingleLambdaNormActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- Log of the root image radius in terms of the normalized coefficient and `log P`. -/
theorem log_rootImageRadius_eq_neg_coefficient_mul_logP :
    Real.log (rootImageRadius T b : Real) =
      -((qVFamNormalizedCoefficient T b / (2 * (l.value : Real))) *
        Real.log (qVFamTensorP T b : Real)) := by
  rw [rootImageRadius_eq_rootNorm]
  rw [rootNormedElementNorm_eq_p_rpow]
  change Real.log
      (((qVFamTensorP T b : Real) ^
        (-(qVFamNormalizedCoefficient T b) / (2 * (l.value : Real))))) = _
  rw [Real.log_rpow (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)]
  ring

variable {T}
/-- Root normed log-volume in terms of the source q unit norm. -/
theorem rootNormedLogVolume_eq_inv_twoL_mul_log_norm :
    rootNormedLogVolume T b =
      (1 / (2 * (l.value : Real))) *
        Real.log ‖(sourceRootQUnit T b : rootBase T b)‖ := by
  unfold rootNormedLogVolume
  change Real.log ‖(rootNormedElement T b : rootNormedAmbient T b)‖ =
    (1 / (2 * (l.value : Real))) *
      Real.log ‖(sourceRootQUnit T b : rootBase T b)‖
  rw [show ‖(rootNormedElement T b : rootNormedAmbient T b)‖ =
    rootNormedElementNorm T b from rfl]
  have h := congrArg Real.log (rootNormedElementNorm_pow_twoL (T := T) (b := b))
  rw [Real.log_pow] at h
  have h2 : ((2 * l.value : Nat) : Real) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (by norm_num) l.prime.ne_zero
  rw [← h]
  rw [show (1 / (2 * (l.value : Real))) = (2 * (l.value : Real))⁻¹ by ring]
  rw [show ((↑(2 * l.value) : Real)) = 2 * (l.value : Real) from by push_cast; ring]
  have h2' : (2 * (l.value : Real)) ≠ 0 := by
    have hc : ((2 * l.value : Nat) : Real) ≠ 0 := h2
    push_cast at hc ⊢
    exact hc
  rw [inv_mul_cancel_left₀ h2']

def rootRadiusBridgeRows : List (String × String × String) :=
  [ ("log_rootImageRadius_eq_neg_coefficient_mul_logP", "log(rootImageRadius) = -(c_norm/(2l)) log P", "PROVED (S709 donors)"),
    ("rootNormedLogVolume_eq_inv_twoL_mul_log_norm", "rootNormedLogVolume = (1/2l) log||q||", "PROVED (S201 donors)") ]

theorem rootRadiusBridgeRows_length : rootRadiusBridgeRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1RootRadiusBridgeActual

end