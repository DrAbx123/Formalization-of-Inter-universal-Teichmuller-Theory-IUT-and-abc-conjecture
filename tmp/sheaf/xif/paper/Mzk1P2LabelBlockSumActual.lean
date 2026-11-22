/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P2LabelBlockCoefficientActual
import tmp.sheaf.xif.paper.Mzk1RootExtensionUltrametricActual
import Mathlib.Tactic

/-! # P2 (R1.2) multi-label sum: `g^q_a = sum_i c_ia g^theta_i` integral -/

/-
| field | value |
|---|---|
| Status | PROVED multi-label prototype: if all theta generators and all coefficients lie in the tensor integer ring, then the R1.2 q generator `sum_i c_i * theta_i` lies in it (uses `rootNormedExtension_norm_add_le_max` for the ultrametric sum bound) |
| GAP | actual source maps (native q reading -> root expansion; theta allowed image -> lambda) and multi-index tensor landing are still not constructed; the label block here is a named structure of already-integral generators, not a source construction |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockSumActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteC0RootQLatticeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RootExtensionUltrametricActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionFieldScalingActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Zero is in the tensor integer ring. -/
theorem p2_productUnitBall_zero_mem :
    (0 : RootExtensionProductCarrier T) ∈ rootExtensionProductUnitBall T := by
  rw [rootExtensionProductUnitBall]
  intro b _
  unfold rootExtensionUnitBall
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [sub_zero, Pi.zero_apply, norm_zero]
  norm_num

/-- Products of integral elements are integral in the tensor ring. -/
theorem p2_productUnitBall_mul_mem
    {x y : RootExtensionProductCarrier T}
    (hx : x ∈ rootExtensionProductUnitBall T)
    (hy : y ∈ rootExtensionProductUnitBall T) :
    (fun b => x b * y b) ∈ rootExtensionProductUnitBall T := by
  rw [rootExtensionProductUnitBall] at hx hy ⊢
  intro b _
  have hxb : x b ∈ rootExtensionUnitBall T b := hx b (Set.mem_univ b)
  have hyb : y b ∈ rootExtensionUnitBall T b := hy b (Set.mem_univ b)
  unfold rootExtensionUnitBall at hxb hyb ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hxb hyb ⊢
  simp only [sub_zero] at hxb hyb ⊢
  calc ‖x b * y b‖ = ‖x b‖ * ‖y b‖ := norm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul hxb hyb (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

/-- Sums of integral elements are integral in the tensor ring (ultrametric bound). -/
theorem p2_productUnitBall_add_mem
    {x y : RootExtensionProductCarrier T}
    (hx : x ∈ rootExtensionProductUnitBall T)
    (hy : y ∈ rootExtensionProductUnitBall T) :
    x + y ∈ rootExtensionProductUnitBall T := by
  rw [rootExtensionProductUnitBall] at hx hy ⊢
  intro b _
  have hxb : x b ∈ rootExtensionUnitBall T b := hx b (Set.mem_univ b)
  have hyb : y b ∈ rootExtensionUnitBall T b := hy b (Set.mem_univ b)
  unfold rootExtensionUnitBall at hxb hyb ⊢
  rw [Metric.mem_closedBall, dist_eq_norm] at hxb hyb ⊢
  simp only [sub_zero, Pi.add_apply] at hxb hyb ⊢
  calc ‖x b + y b‖ ≤ max ‖x b‖ ‖y b‖ :=
        rootNormedExtension_norm_add_le_max T b _ _
    _ ≤ 1 := max_le hxb hyb

/-- Multi-label label-block data: theta generators and coefficients in the tensor
integer ring. -/
structure P2LabelBlockSumData (ι : Type*) [Fintype ι] where
  thetaGen : ι → RootExtensionProductCarrier T
  theta_mem : ∀ i, thetaGen i ∈ rootExtensionProductUnitBall T
  coeff : ι → RootExtensionProductCarrier T
  coeff_mem : ∀ i, coeff i ∈ rootExtensionProductUnitBall T

/-- **R1.2 multi-label**: the q generator `sum_i c_i * theta_i` is integral. -/
theorem p2_labelBlockSum_qGen_mem
    {ι : Type*} [Fintype ι] (D : P2LabelBlockSumData T ι) :
    (fun b => ∑ i, D.coeff i b * D.thetaGen i b) ∈
      rootExtensionProductUnitBall T := by
  classical
  have hterm : ∀ i, (fun b => D.coeff i b * D.thetaGen i b) ∈
      rootExtensionProductUnitBall T :=
    fun i => p2_productUnitBall_mul_mem T (D.coeff_mem i) (D.theta_mem i)
  have hsum : (∑ i : ι, (fun b => D.coeff i b * D.thetaGen i b)) ∈
      rootExtensionProductUnitBall T := by
    refine Finset.induction_on (Finset.univ : Finset ι) ?base ?step
    · simpa using p2_productUnitBall_zero_mem T
    · intro i s hi ih
      rw [Finset.sum_insert hi]
      exact p2_productUnitBall_add_mem T (hterm i) ih
  have hfun : (fun b => ∑ i, D.coeff i b * D.thetaGen i b) =
      ∑ i : ι, (fun b => D.coeff i b * D.thetaGen i b) := by
    ext b
    rw [Finset.sum_apply]
  rw [hfun]
  exact hsum

end LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockSumActual