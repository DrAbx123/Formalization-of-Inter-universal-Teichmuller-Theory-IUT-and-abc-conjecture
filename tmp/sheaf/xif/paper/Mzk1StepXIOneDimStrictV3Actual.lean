/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeScalingActual
import tmp.sheaf.xif.paper.PaperRootExtensionPrimeDecompositionActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import Mathlib.Tactic

/-! # A577: strict_measure via SINGLE-coordinate strictness (clean, self-contained)

The q-region is chosen to equal the hull in every coordinate except one:
in coordinate b0 use the strictly smaller radius R_b0/p_b0 (1D p-scaling strict
ball measure), and use the hull radius R_b elsewhere.  Product Haar then has all
factors equal except one strictly smaller, so the product measure is strictly
smaller too (Finset.prod_lt_prod with a single strict factor).  This replaces the
named `strict_measure` by a theorem requiring only the one-dimensional strictness
proved below from the green p-scaling lemmas.

No sorry/axiom; 1D lemmas are self-contained copies of the p-scaling proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIOneDimStrictV3Actual

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
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open MeasureTheory
open scoped Pointwise ENNReal BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. One-dimensional p-scaling strict ball measure -/

noncomputable def primeFactor : Real :=
  (‖(algebraMap ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
      (qVFamTensorP T b) : rootNormedExtension T b)‖) ^
    Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)

theorem primeFactor_pos : 0 < primeFactor T b := by
  unfold primeFactor
  rw [rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p]
  apply pow_pos
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).pos)

theorem primeFactor_lt_one : primeFactor T b < 1 := by
  unfold primeFactor
  rw [rootNorm_algebraMap_prime (T := T) (b := b), Padic.norm_p]
  have hp : (1 : Real) < (qVFamTensorP T b : Real) :=
    by exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
  have hinv : (qVFamTensorP T b : Real)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hnonneg : (0 : Real) ≤ (qVFamTensorP T b : Real)⁻¹ := by positivity
  have hd : Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) ≠ 0 :=
    Nat.ne_of_gt Module.finrank_pos
  exact pow_lt_one₀ hnonneg hinv hd

theorem prime_smul_closedBall (R : Real) (hR : 0 ≤ R) :
    (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
        Metric.closedBall (0 : rootNormedExtension T b) R =
      Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : Real)) := by
  rw [show (qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
        Metric.closedBall (0 : rootNormedExtension T b) R =
      Metric.closedBall ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)]) •
        (0 : rootNormedExtension T b))
        (‖(qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])‖ * R) from
    _root_.smul_closedBall _ _ hR]
  rw [smul_zero]
  congr 1
  rw [Padic.norm_p, div_eq_inv_mul, mul_comm]

theorem rootExtensionHaar_ball_strict (R : Real) (hR : 0 < R) :
    rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
        (R / (qVFamTensorP T b : Real))) <
      rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) := by
  have hsm := rootPrime_smul_measure (T := T) (b := b)
    (Metric.closedBall (0 : rootNormedExtension T b) R)
  rw [prime_smul_closedBall T b R hR.le] at hsm
  have hfinF : rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b) R
  have hfinH : rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (R / (qVFamTensorP T b : Real))) < ⊤ :=
    rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _
  have hposF : 0 < rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b) R) :=
    rootExtensionClosedBall_measure_pos (T := T) (b := b) R hR
  have hto : (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
      (R / (qVFamTensorP T b : Real)))).toReal =
      primeFactor T b * (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal := by
    rw [hsm, ENNReal.toReal_mul]
    congr 1
    unfold primeFactor
    exact ENNReal.toReal_ofReal (le_of_lt (primeFactor_pos T b))
  refine (ENNReal.toReal_lt_toReal (ne_of_lt hfinH) (ne_of_lt hfinF)).mp ?_
  have hposFreal : 0 < (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hposF) (ne_of_lt hfinF)
  rw [hto]
  calc primeFactor T b * (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal
      < 1 * (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal :=
        mul_lt_mul_of_pos_right (primeFactor_lt_one T b) hposFreal
    _ = (rootExtensionHaar T b
        (Metric.closedBall (0 : rootNormedExtension T b) R)).toReal := one_mul _

/-! ## 2. Single-coordinate product region: strict Haar increase -/

variable [Nonempty (Bad (nativePlaceSelection T))]

/-- The `R/p` radius. -/
noncomputable def rpRadius (b : Bad (nativePlaceSelection T)) : Real :=
  (rootImageRadius T b : Real) / (qVFamTensorP T b : Real)

theorem rpRadius_pos (b : Bad (nativePlaceSelection T)) : 0 < rpRadius T b := by
  unfold rpRadius
  have hR : (0 : Real) < (rootImageRadius T b : Real) := by
    exact_mod_cast rootImageRadius_pos T b
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

/-- The hull as a product of `R_b` balls. -/
noncomputable def hullRegion : Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b)
    (rootImageRadius T b : Real))

theorem hullRegion_eq_s1902Hull : hullRegion T = s1902Hull T := rfl

/-- The single-coordinate strict region: `R_{b0}/p_{b0}` in coordinate b0 and the
hull radius `R_b` in every other coordinate. -/
noncomputable def oneCoordRegion (b0 : Bad (nativePlaceSelection T)) :
    Set (S1902Carrier T) :=
  Set.pi Set.univ (fun b => Metric.closedBall (0 : rootNormedExtension T b)
    (if b = b0 then rpRadius T b else (rootImageRadius T b : Real)))

theorem oneCoordRegion_subset_hull (b0 : Bad (nativePlaceSelection T)) :
    oneCoordRegion T b0 <= hullRegion T := by
  intro x hx b _
  have hxb := hx b (Set.mem_univ b)
  rw [oneCoordRegion, Set.mem_pi] at hx
  rw [Metric.mem_closedBall] at hxb ⊢
  rw [dist_zero_right] at hxb ⊢
  by_cases h : b = b0
  · rw [if_pos h] at hxb
    exact le_trans hxb (rpRadius_le_radius T b)
  · rw [if_neg h] at hxb
    exact hxb

theorem oneCoordRegion_measure_pos (b0 : Bad (nativePlaceSelection T)) :
    0 < rootExtensionProductHaar T (oneCoordRegion T b0) := by
  unfold oneCoordRegion rootExtensionProductHaar
  rw [Measure.pi_pi, pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr (fun b _ => by
    by_cases h : b = b0
    · rw [if_pos h]
      exact ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _
        (rpRadius_pos T b))
    · rw [if_neg h]
      have hR : (0 : Real) < (rootImageRadius T b : Real) := by
        exact_mod_cast rootImageRadius_pos T b
      exact ne_of_gt (rootExtensionClosedBall_measure_pos (T := T) (b := b) _ hR))

theorem oneCoordRegion_measure_lt_top (b0 : Bad (nativePlaceSelection T)) :
    rootExtensionProductHaar T (oneCoordRegion T b0) < ⊤ := by
  unfold oneCoordRegion rootExtensionProductHaar
  rw [Measure.pi_pi]
  apply ENNReal.prod_lt_top
  intro b _
  by_cases h : b = b0
  · rw [if_pos h]
    exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _
  · rw [if_neg h]
    exact rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _

theorem hullRegion_measure_lt_top : rootExtensionProductHaar T (hullRegion T) < ⊤ := by
  rw [hullRegion_eq_s1902Hull]
  exact (rootExtensionProductImageHull_measure_pos_lt_top (T := T)).2

theorem oneCoordRegion_toReal (b0 : Bad (nativePlaceSelection T)) :
    (rootExtensionProductHaar T (oneCoordRegion T b0)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (if b = b0 then rpRadius T b else (rootImageRadius T b : Real)))).toReal := by
  unfold oneCoordRegion rootExtensionProductHaar
  rw [Measure.pi_pi, ENNReal.toReal_prod]

theorem hullRegion_toReal :
    (rootExtensionProductHaar T (hullRegion T)).toReal =
      ∏ b : Bad (nativePlaceSelection T),
        (rootExtensionHaar T b (Metric.closedBall (0 : rootNormedExtension T b)
          (rootImageRadius T b : Real))).toReal := by
  unfold hullRegion rootExtensionProductHaar
  rw [Measure.pi_pi, ENNReal.toReal_prod]

/-- **Single-coordinate strictness**: the product measure is strictly smaller, with
all factors equal except the one strictly-smaller coordinate b0. -/
theorem oneCoordRegion_toReal_lt_hull (b0 : Bad (nativePlaceSelection T)) :
    (rootExtensionProductHaar T (oneCoordRegion T b0)).toReal <
      (rootExtensionProductHaar T (hullRegion T)).toReal := by
  rw [oneCoordRegion_toReal, hullRegion_toReal]
  refine Finset.prod_lt_prod (fun b _ => ?_) ?_
  · by_cases h : b = b0
    · rw [if_pos h]
      have hR : (0 : Real) < (rootImageRadius T b : Real) := by
        exact_mod_cast rootImageRadius_pos T b
      refine le_of_lt ((ENNReal.toReal_lt_toReal
        (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))
        (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b) _))).mpr ?_)
      simpa using rootExtensionHaar_ball_strict T b (rootImageRadius T b) hR
    · rw [if_neg h]
      exact le_of_eq rfl
  · refine ⟨b0, Finset.mem_univ b0, ?_⟩
    rw [if_pos rfl]
    have hR : (0 : Real) < (rootImageRadius T b0 : Real) := by
      exact_mod_cast rootImageRadius_pos T b0
    exact (ENNReal.toReal_lt_toReal
      (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b0) _))
      (ne_of_lt (rootExtensionClosedBall_measure_lt_top (T := T) (b := b0) _))).mpr
      (by simpa using rootExtensionHaar_ball_strict T b0 (rootImageRadius T b0) hR)

theorem oneCoordRegion_haarStrict (b0 : Bad (nativePlaceSelection T)) :
    rootExtensionProductHaar T (oneCoordRegion T b0) <
      rootExtensionProductHaar T (hullRegion T) :=
  (ENNReal.toReal_lt_toReal (ne_of_lt (oneCoordRegion_measure_lt_top T b0))
    (ne_of_lt (hullRegion_measure_lt_top T))).mp (oneCoordRegion_toReal_lt_hull T b0)

/-- Volume functional from the product Haar. -/
noncomputable def coordVolume (S : Set (S1902Carrier T)) : Real :=
  (rootExtensionProductHaar T S).toReal

/-- The xi-e requirement with SINGLE-coordinate strictness: `q_pos` and
`strict_measure` are both theorems (no named strict_measure). -/
noncomputable def singleCoordRequirement (b0 : Bad (nativePlaceSelection T)) :
    XiEContainmentRequirement (S1902Carrier T) (coordVolume T) where
  qRegion := oneCoordRegion T b0
  thetaPossibleImages := oneCoordRegion T b0
  hullRegion := s1902Hull T
  q_in_possible := fun _ hx => hx
  possible_in_hull := by
    intro x hx
    exact oneCoordRegion_subset_hull T b0 (by simpa [hullRegion_eq_s1902Hull] using hx)
  q_pos := ENNReal.toReal_pos (ne_of_gt (oneCoordRegion_measure_pos T b0))
    (ne_of_lt (oneCoordRegion_measure_lt_top T b0))
  strict_measure := by
    have h : coordVolume T (oneCoordRegion T b0) < coordVolume T (hullRegion T) :=
      oneCoordRegion_toReal_lt_hull T b0
    simpa [coordVolume, hullRegion_eq_s1902Hull] using h

theorem singleCoord_cor312 (b0 : Bad (nativePlaceSelection T))
    (hqneg : requirementSignedQ (singleCoordRequirement T b0) < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion
      (requirementContract (singleCoordRequirement T b0) hqneg ipl hipl she hshe apt hapt) :=
  requirement_cor312 (singleCoordRequirement T b0) hqneg ipl hipl she hshe apt hapt

/-- Status row: single-coordinate strictness has replaced the named strict_measure. -/
def singleCoordRows : List (String × String × String) :=
  [ ("1D strict ball measure", "rootExtensionHaar_ball_strict", "PROVED (p-scaling)"),
    ("single-coordinate region", "oneCoordRegion (R/p in b0, R elsewhere)", "DEF"),
    ("containment / positivity", "oneCoordRegion_subset_hull / measure_pos", "PROVED"),
    ("strict Haar increase", "oneCoordRegion_haarStrict", "PROVED (single strict factor)"),
    ("strict_measure", "singleCoordRequirement.strict_measure", "PROVED (no named field)"),
    ("scope", "conditional Cor312Conclusion; no ABC closure", "INTEGRITY") ]

theorem singleCoordRows_length : singleCoordRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIOneDimStrictV3Actual

end