/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-!
# A558 annulus measure with the p-radius (R/p), NOT R/2

In a nonarchimedean field `|2| = 1`, so `closedBall 0 (R/2) = closedBall 0 R`; the
correct strict scaling is by the residue characteristic `p_b`:
`p_b • closedBall 0 R = closedBall 0 (R/p_b)` and the p-adic Haar scaling gives
`μ(ball R) = p_b^d * μ(ball (R/p_b))`.  Product-wise this strictly increases the
Haar measure from the `R/p`-ball region to the full `R`-ball region `= s1902Hull`,
so the annulus has POSITIVE measure (last named input resolved).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasurePrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-! ## 1. Local p-scaling of a ball -/

variable (b : Bad (nativePlaceSelection T))

/-- The residue characteristic as a `ℚ_p`-scalar. -/
noncomputable def pScalar : ℚ_[(qVFamTensorP T b)] :=
  (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])

theorem pScalar_norm : ‖pScalar T b‖ = (qVFamTensorP T b : ℝ)⁻¹ :=
  Padic.norm_p

/-- `p • closedBall 0 R = closedBall 0 (R/p)`. -/
theorem pScalar_smul_closedBall (R : ℝ) (hR : 0 ≤ R) :
    pScalar T b • Metric.closedBall (0 : rootNormedExtension T b) R =
      Metric.closedBall (0 : rootNormedExtension T b) (R / (qVFamTensorP T b : ℝ)) := by
  rw [smul_closedBall _ _ hR, pScalar_norm]
  congr 1
  rw [div_eq_inv_mul]

/-- The p-adic dimension of the local root extension. -/
noncomputable def localDim : ℕ :=
  Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)

theorem localDim_pos : 0 < localDim T b :=
  Module.finrank_pos

/-- **Local strict ball ratio**: `μ(ball R) = p^d * μ(ball (R/p))`. -/
theorem rootExtensionHaar_ball_ratio (R : ℝ) (hR : 0 ≤ R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) =
      ((qVFamTensorP T b : ENNReal) ^ localDim T b) *
        rootExtensionHaar T b
          (Metric.closedBall (0 : rootNormedExtension T b)
            (R / (qVFamTensorP T b : ℝ))) := by
  have h := FinitePadicHaarScaling.measure_prime_smul_finiteDimensional
    (p := qVFamTensorP T b) (M := rootNormedExtension T b)
    (rootExtensionHaar T b) (Metric.closedBall (0 : rootNormedExtension T b) R)
  rw [pScalar_smul_closedBall T b R hR] at h
  have hdim0 : ((qVFamTensorP T b : ENNReal) ^ localDim T b) ≠ 0 :=
    ENNReal.pow_ne_zero (ENNReal.natCast_ne_top _) _
  have hdimtop : ((qVFamTensorP T b : ENNReal) ^ localDim T b) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top _) _
  calc rootExtensionHaar T b (Metric.closedBall 0 R)
      = ((qVFamTensorP T b : ENNReal) ^ localDim T b) *
          (((qVFamTensorP T b : ENNReal) ^ localDim T b)⁻¹ *
            rootExtensionHaar T b (Metric.closedBall 0 R)) := by
        rw [ENNReal.mul_inv_cancel hdim0 hdimtop, one_mul]
    _ = ((qVFamTensorP T b : ENNReal) ^ localDim T b) *
          rootExtensionHaar T b
            (Metric.closedBall 0 (R / (qVFamTensorP T b : ℝ))) := by rw [← h]

/-! ## 2. Product regions and the annulus -/

/-- Full product ball: `s1902Hull` (product of the full-radius balls). -/
def fullBallRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : rootNormedExtension T b) (rootImageRadius T b : ℝ))

/-- The p-scaled (strictly smaller) product ball: radius `R_b / p_b`. -/
def primeHalfBallRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : rootNormedExtension T b)
      ((rootImageRadius T b : ℝ) / (qVFamTensorP T b : ℝ)))

/-- The full product ball IS the actual hull. -/
theorem fullBallRegion_eq_hull : fullBallRegion T = s1902Hull T := rfl

theorem primeHalfBallRegion_subset_full :
    primeHalfBallRegion T ⊆ fullBallRegion T := by
  intro x hx b _
  have hxb := hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall] at hxb ⊢
  rw [dist_zero_right] at hxb ⊢
  have hp : (1 : ℝ) ≤ (qVFamTensorP T b : ℝ) :=
    Nat.one_le_cast.mpr (Fact.out : Nat.Prime (qVFamTensorP T b)).pos
  have hnonneg : (0 : ℝ) ≤ (rootImageRadius T b : ℝ) := NNReal.coe_nonneg _
  calc ‖x b‖ ≤ (rootImageRadius T b : ℝ) / (qVFamTensorP T b : ℝ) := hxb
    _ ≤ (rootImageRadius T b : ℝ) / 1 := by gcongr
    _ = (rootImageRadius T b : ℝ) := div_one _

end

end LeanFormal.IUT.XiFPaper.Mzk1AnnulusMeasurePrimeActual