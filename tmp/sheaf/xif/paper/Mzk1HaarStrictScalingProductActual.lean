/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import Mathlib.Tactic

/-! # A578: strict_measure resolved via 1D strictness + real product comparison

The one-dimensional p-scaling strictness lives in the green 1D file
(`Mzk1HaarScalingOneDimActual.rootExtensionHaar_ball_strict`).  Here we form the
all-coordinate R/p product region `rpRegion`, compare the product Haar measures in
the reals using `Finset.prod_lt_prod` (each factor positive, each factor at most the
hull factor, one factor strictly smaller), convert back with
`ENNReal.toReal_lt_toReal`, and obtain the strict measure as a THEOREM: no named
`strict_measure` remains.  The resulting xi-e requirement gives the conditional
Cor312Conclusion through the green `requirement_cor312`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual

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
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeDecompositionActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionPrimeScalingActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

variable (b0 : Bad (nativePlaceSelection T))

/-- Local 1D p-scaling strictness (self-contained, extensional proof). -/
theorem prime_smul_closedBall (R : Real) (hR : 0 <= R) :
    (qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)]) •
        Metric.closedBall (0 : rootNormedExtension T b0) R =
      Metric.closedBall (0 : rootNormedExtension T b0)
        (R / (qVFamTensorP T b0 : Real)) := by
  have hp_pos : (0 : Real) < (qVFamTensorP T b0 : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b0)).pos
  have hp_ne_real : (qVFamTensorP T b0 : Real) ≠ 0 := ne_of_gt hp_pos
  have hpK_ne : (qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)]) ≠ 0 := by
    have hpos : (0 : Real) < ‖((qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)]))‖ := by
      rw [Padic.norm_p]
      positivity
    exact norm_pos_iff.mp hpos
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
    dsimp only
    have hsm : (qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)]) • y =
        algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
          (qVFamTensorP T b0) * y := (Algebra.smul_def _ _)
    rw [hsm, norm_mul, rootNorm_algebraMap_prime, Padic.norm_p]
    calc (qVFamTensorP T b0 : Real)⁻¹ * ‖y‖ <=
          (qVFamTensorP T b0 : Real)⁻¹ * R := by gcongr
      _ = R / (qVFamTensorP T b0 : Real) := by rw [div_eq_inv_mul]
  · rintro hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    refine ⟨(qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)])⁻¹ • x, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hsm : (qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)])⁻¹ • x =
          algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
            ((qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)])⁻¹) * x :=
        (Algebra.smul_def _ _)
      rw [hsm, norm_mul]
      have hnorm : ‖algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
          ((qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)])⁻¹)‖ =
          (qVFamTensorP T b0 : Real) := by
        rw [map_inv₀, norm_inv, rootNorm_algebraMap_prime, Padic.norm_p, inv_inv]
      rw [hnorm]
      calc (qVFamTensorP T b0 : Real) * ‖x‖ <=
            (qVFamTensorP T b0 : Real) * (R / (qVFamTensorP T b0 : Real)) := by gcongr
        _ = R := by field_simp [hp_ne_real]
    · change (qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)]) •
        ((qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)])⁻¹ • x) = x
      exact smul_inv_smul₀ hpK_ne x

theorem rootExtensionHaar_ball_strict (R : Real) (hR : 0 < R) :
    rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0)
        (R / (qVFamTensorP T b0 : Real))) <
      rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0) R) := by
  have hsm := rootPrime_smul_measure (T := T) (b := b0)
    (Metric.closedBall (0 : rootNormedExtension T b0) R)
  rw [prime_smul_closedBall T b0 R hR.le] at hsm
  have hfinF : rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0) R) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b0) R
  have hfinH : rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0)
      (R / (qVFamTensorP T b0 : Real))) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b0) _
  have hposF : 0 < rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0) R) :=
    rootExtensionClosedBall_measure_pos (T := T) (b := b0) R hR
  have hto : (rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0)
      (R / (qVFamTensorP T b0 : Real)))).toReal =
      (ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
        (qVFamTensorP T b0) : rootNormedExtension T b0)‖ ^
          Module.finrank ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0))).toReal *
        (rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0) R)).toReal := by
    rw [hsm, ENNReal.toReal_mul]
  have hfac : (ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
      (qVFamTensorP T b0) : rootNormedExtension T b0)‖ ^
        Module.finrank ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0))).toReal < 1 := by
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hnorm : ‖(algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
        (qVFamTensorP T b0 : ℚ_[(qVFamTensorP T b0)]) : rootNormedExtension T b0)‖ =
        (qVFamTensorP T b0 : Real)⁻¹ := by
      rw [rootNorm_algebraMap_prime (T := T) (b := b0), Padic.norm_p]
    rw [hnorm]
    have hp : (1 : Real) < (qVFamTensorP T b0 : Real) := by
      exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b0)).one_lt
    have hinv : (qVFamTensorP T b0 : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
    have hnonneg : (0 : Real) <= (qVFamTensorP T b0 : Real)⁻¹ := by positivity
    have hd : Module.finrank ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0) ≠ 0 :=
      Nat.ne_of_gt Module.finrank_pos
    exact pow_lt_one₀ hnonneg hinv hd
  refine (ENNReal.toReal_lt_toReal (ne_of_lt hfinH) (ne_of_lt hfinF)).mp ?_
  rw [hto]
  calc (ENNReal.ofReal (‖(algebraMap ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0)
        (qVFamTensorP T b0) : rootNormedExtension T b0)‖ ^
          Module.finrank ℚ_[(qVFamTensorP T b0)] (rootNormedExtension T b0))).toReal *
        (rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0) R)).toReal
      < 1 * (rootExtensionHaar T b0 (Metric.closedBall
          (0 : rootNormedExtension T b0) R)).toReal := by
        exact mul_lt_mul_of_pos_right hfac
          (ENNReal.toReal_pos (ne_of_gt hposF) (ne_of_lt hfinF))
    _ = (rootExtensionHaar T b0 (Metric.closedBall (0 : rootNormedExtension T b0) R)).toReal :=
        one_mul _
/-- The `R/p` radius. -/
noncomputable def rpRadius (b : Bad (nativePlaceSelection T)) : Real :=
  (rootImageRadius T b : Real) / (qVFamTensorP T b : Real)

theorem rpRadius_pos (b : Bad (nativePlaceSelection T)) : 0 < rpRadius T b := by
  unfold rpRadius
  have hR : (0 : Real) < (rootImageRadius T b : Real) := by
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  have hp : (1 : Real) < (qVFamTensorP T b : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  exact div_pos hR (by linarith)

theorem rpRadius_le_radius (b : Bad (nativePlaceSelection T)) :
    rpRadius T b <= (rootImageRadius T b : Real) := by
  unfold rpRadius
  have hR : (0 : Real) <= (rootImageRadius T b : Real) := NNReal.coe_nonneg _
  have hp : (1 : Real) <= (qVFamTensorP T b : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt.le
  rw [div_le_iff₀ (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)]
  nlinarith

/-- The all-coordinate `R/p` region. -/
noncomputable def rpRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b)
    (rpRadius T b))

/-- The hull product region. -/
noncomputable def hullRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b)
    (rootImageRadius T b : Real))

theorem hullRegion_eq_s1902Hull : hullRegion T = s1902Hull T := rfl

theorem rpRegion_subset_hull : rpRegion T <= hullRegion T := by
  intro x hx b _
  have hxb := hx b (Set.mem_univ b)
  rw [Metric.mem_closedBall, dist_zero_right] at hxb
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_trans hxb (rpRadius_le_radius T b)

theorem rpRegion_measure_pos : 0 < rootExtensionProductHaar T (rpRegion T) := by
  unfold rpRegion rootExtensionProductHaar
  rw [Measure.pi_pi, pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ =>
    ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _
      (rpRadius_pos T b)))

theorem rpRegion_measure_lt_top : rootExtensionProductHaar T (rpRegion T) < ⊤ := by
  unfold rpRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

theorem hullRegion_measure_lt_top : rootExtensionProductHaar T (hullRegion T) < ⊤ := by
  rw [hullRegion_eq_s1902Hull]
  exact (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2

theorem rpRegion_toReal :
    (rootExtensionProductHaar T (rpRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rpRadius T b))).toReal := by
  unfold rpRegion rootExtensionProductHaar
  rw [Measure.pi_pi, ENNReal.toReal_prod]

theorem hullRegion_toReal :
    (rootExtensionProductHaar T (hullRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rootImageRadius T b : Real))).toReal := by
  unfold hullRegion rootExtensionProductHaar
  rw [Measure.pi_pi, ENNReal.toReal_prod]

/-- 1D strictness transported to the real-valued factors. -/
theorem oneD_toReal_lt (b : Bad (nativePlaceSelection T)) :
    (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rpRadius T b))).toReal <
      (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (rootImageRadius T b : Real))).toReal := by
  have hR : (0 : Real) < (rootImageRadius T b : Real) := by
    exact_mod_cast rootImageRadius_pos (T := T) (b := b)
  exact (ENNReal.toReal_lt_toReal
    (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))
    (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))).mpr
    (by simpa [rpRadius] using rootExtensionHaar_ball_strict T b (rootImageRadius T b) hR)

theorem oneD_toReal_pos (b : Bad (nativePlaceSelection T)) :
    0 < (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (rpRadius T b))).toReal := by
  exact ENNReal.toReal_pos
    (ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _
      (rpRadius_pos T b)))
    (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))

/-- **Product strictness in the reals**: one strictly smaller factor plus all factors
positive and at most the hull factor. -/
theorem rpRegion_toReal_lt_hull :
    (rootExtensionProductHaar T (rpRegion T)).toReal <
      (rootExtensionProductHaar T (hullRegion T)).toReal := by
  rw [rpRegion_toReal, hullRegion_toReal]
  refine Finset.prod_lt_prod (fun b _ => oneD_toReal_pos T b)
    (fun b _ => le_of_lt (oneD_toReal_lt T b)) ?_
  exact ⟨Classical.choice inferInstance, Finset.mem_univ _,
    oneD_toReal_lt T (Classical.choice inferInstance)⟩

/-- **Strict Haar increase (ENNReal)**: no named field. -/
theorem rpRegion_haarStrict :
    rootExtensionProductHaar T (rpRegion T) <
      rootExtensionProductHaar T (s1902Hull T) := by
  rw [← hullRegion_eq_s1902Hull]
  exact (ENNReal.toReal_lt_toReal (ne_of_lt (rpRegion_measure_lt_top T))
    (ne_of_lt (hullRegion_measure_lt_top T))).mp (rpRegion_toReal_lt_hull T)

/-- Volume functional. -/
noncomputable def rpVolume (S : Set (S1902Carrier T)) : Real :=
  (rootExtensionProductHaar T S).toReal

theorem rpVolume_strict : rpVolume T (rpRegion T) < rpVolume T (s1902Hull T) := by
  have h := rpRegion_toReal_lt_hull T
  simpa [rpVolume, hullRegion_eq_s1902Hull] using h

/-- The xi-e requirement with `q_pos` and `strict_measure` both PROVED. -/
noncomputable def rpRequirement :
    XiEContainmentRequirement (S1902Carrier T) (rpVolume T) where
  qRegion := rpRegion T
  thetaPossibleImages := rpRegion T
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := by
    intro x hx
    have hx' : x ∈ hullRegion T := rpRegion_subset_hull T hx
    simpa [hullRegion_eq_s1902Hull] using hx'
  q_pos := ENNReal.toReal_pos (ne_of_gt (rpRegion_measure_pos T))
    (ne_of_lt (rpRegion_measure_lt_top T))
  strict_measure := rpVolume_strict T

theorem rp_cor312 (hqneg : requirementSignedQ (rpRequirement T) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (rpRequirement T) hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 (rpRequirement T) hqneg ipl hipl she hshe apt hapt

/-- Status: strict_measure is a theorem here (1D p-scaling + real product). -/
def scalingProductRows : List (String × String × String) :=
  [ ("1D strict ball measure", "rootExtensionHaar_ball_strict (1D file)", "PROVED (p-scaling)"),
    ("product R/p region", "rpRegion", "DEF"),
    ("factor positivity/upper bounds", "oneD_toReal_pos / oneD_toReal_lt", "PROVED"),
    ("real product strictness", "Finset.prod_lt_prod", "PROVED"),
    ("strict Haar increase", "rpRegion_haarStrict", "PROVED"),
    ("strict_measure", "rpRequirement.strict_measure", "PROVED (no named field)"),
    ("scope", "conditional Cor312Conclusion; no ABC closure", "INTEGRITY") ]

theorem scalingProductRows_length : scalingProductRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1HaarStrictScalingProductActual

end