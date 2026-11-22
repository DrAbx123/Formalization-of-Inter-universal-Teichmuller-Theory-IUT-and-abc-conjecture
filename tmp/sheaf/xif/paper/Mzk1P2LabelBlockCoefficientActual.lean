/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RouteC0RootQLatticeV2Actual
import Mathlib.Tactic

/-! # P2 (R1.2) prototype: label-block coefficient integrality (no old C3) -/

/-
| field | value |
|---|---|
| Status | PROVED rank-one prototype: `c_b = qhat_b / lambda_b` is integral (`p2Coefficient_mem_unitBall`); pure-tensor coefficient family integral; label-block q generator integral when theta generators and coefficients are integral |
| GAP | old C3 is empty (`S1429CompletionRootObstructionActual.sourcePilotRegionData_isEmpty`), so old `tensorLanding_q` cannot be used; native source q-reading -> root expansion and actual theta allowed-image maps are not constructed; the tensor model here is the actual product carrier (finite product of O_{L_b}), not a literal `TensorProduct` over a common base |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The R1.2 rank-one coefficient `c_b = qhat_b / lambda_b`. -/
noncomputable def p2Coefficient
    (b : Bad (nativePlaceSelection T)) : rootNormedExtension T b :=
  c0QHat T b / rootThetaFieldLambda T b

/-- The rank-one coefficient is integral: `c_b ∈ O_{L_b}` (unit ball model). -/
theorem p2Coefficient_norm_le_one
    (b : Bad (nativePlaceSelection T)) : ‖p2Coefficient T b‖ ≤ 1 := by
  have hq := c0QHat_norm_le_radius T b
  have hlam : (rootImageRadius T b : Real) =
      ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ :=
    rootImageRadius_eq_norm_fieldLambda T b
  have hpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← hlam]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  unfold p2Coefficient
  rw [norm_div]
  exact (div_le_one hpos).mpr (by rw [← hlam]; exact hq)

/-- `c_b` lies in the integral lattice `O_{L_b}` (as a set-level unit ball). -/
theorem p2Coefficient_mem_unitBall
    (b : Bad (nativePlaceSelection T)) :
    p2Coefficient T b ∈ rootExtensionUnitBall T b := by
  unfold rootExtensionUnitBall
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa only [sub_zero] using p2Coefficient_norm_le_one T b

/-- `qhat_b = lambda_b * c_b` (the rank-one R1.2 expansion with a single term). -/
theorem p2QHat_eq_lambda_mul_coefficient
    (b : Bad (nativePlaceSelection T)) :
    c0QHat T b = rootThetaFieldLambda T b * p2Coefficient T b := by
  have hpos : 0 < ‖(rootThetaFieldLambda T b : rootNormedExtension T b)‖ := by
    rw [← rootImageRadius_eq_norm_fieldLambda]
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  have hne : rootThetaFieldLambda T b ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hpos)
  unfold p2Coefficient
  field_simp [hne]

/-- Pure tensor of the rank-one coefficients on the actual product carrier. -/
noncomputable def p2PureTensorCoefficient : RootExtensionProductCarrier T :=
  fun b => p2Coefficient T b

/-- The pure tensor `⊗_b c_b` lies in the tensor integer ring (product of `O_{L_b}`). -/
theorem p2PureTensorCoefficient_mem_productUnitBall :
    p2PureTensorCoefficient T ∈ rootExtensionProductUnitBall T := by
  rw [rootExtensionProductUnitBall]
  intro b _
  exact p2Coefficient_mem_unitBall T b

/-- Multiplying by an integral pure tensor preserves integrality. -/
theorem p2_pureTensor_mul_mem
    {x : RootExtensionProductCarrier T}
    (hx : x ∈ rootExtensionProductUnitBall T) :
    (fun b => p2PureTensorCoefficient T b * x b) ∈
      rootExtensionProductUnitBall T := by
  rw [rootExtensionProductUnitBall] at hx ⊢
  intro b _
  have hc : p2PureTensorCoefficient T b ∈ rootExtensionUnitBall T b :=
    p2Coefficient_mem_unitBall T b
  have hxb : x b ∈ rootExtensionUnitBall T b := hx b (Set.mem_univ b)
  unfold rootExtensionUnitBall at hc hxb ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hc hxb ⊢
  simp only [sub_zero] at hc hxb ⊢
  calc ‖p2PureTensorCoefficient T b * x b‖
      = ‖p2PureTensorCoefficient T b‖ * ‖x b‖ := norm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul hc hxb (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

/-- Label-block prototype: actual coefficients and theta generators in the tensor
integer ring, with the q generator defined by the R1.2 expansion (single pure
tensor product here). -/
structure P2LabelBlockData where
  thetaGen : RootExtensionProductCarrier T
  theta_mem : thetaGen ∈ rootExtensionProductUnitBall T
  coeff : RootExtensionProductCarrier T
  coeff_mem : coeff ∈ rootExtensionProductUnitBall T

/-- The label-block q generator `sum_i c_i * theta_i` (one-term rank-one prototype)
is integral. -/
theorem p2_labelBlock_qGen_mem (D : P2LabelBlockData T) :
    (fun b => D.coeff b * D.thetaGen b) ∈ rootExtensionProductUnitBall T := by
  have hc := D.coeff_mem
  have hθ := D.theta_mem
  rw [rootExtensionProductUnitBall] at hc hθ ⊢
  intro b _
  have hcb : D.coeff b ∈ rootExtensionUnitBall T b := hc b (Set.mem_univ b)
  have hθb : D.thetaGen b ∈ rootExtensionUnitBall T b := hθ b (Set.mem_univ b)
  unfold rootExtensionUnitBall at hcb hθb ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hcb hθb ⊢
  simp only [sub_zero] at hcb hθb ⊢
  calc ‖D.coeff b * D.thetaGen b‖ = ‖D.coeff b‖ * ‖D.thetaGen b‖ := norm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul hcb hθb (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

end LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual