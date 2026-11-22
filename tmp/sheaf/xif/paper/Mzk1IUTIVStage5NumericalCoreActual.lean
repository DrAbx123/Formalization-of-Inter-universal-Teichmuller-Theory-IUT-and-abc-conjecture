import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVStage5NumericalCoreActual — dependency-free Stage 5 numerics

The Stage-5 numerical absorption is independent of the ABC dictionary:
from a multiplicative height comparison and a log-volume main estimate one
obtains the additive height form.  This file states and proves that core
numerical implication abstractly, so it can be consumed by any literal-carrier
instantiation.  No closure claim; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalCoreActual

/-- Additive height/weight bound shape (the numerical output of Stage 5). -/
def AdditiveHeightWeightBound (height weight : Nat → Nat → Nat → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ,
    ∀ a b c : Nat, height a b c ≤ (1 + ε) * weight a b c + A

/-- Numerical core: for every `ε > 0` there is `δ > 0` with
`(1 + δ)^2 ≤ 1 + ε`. -/
theorem exists_delta_sq_le_one_add {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (1 + δ) ^ 2 ≤ 1 + ε := by
  refine ⟨min (ε / 4) (1 / 2), ?_, ?_⟩
  · exact lt_min (by positivity) (by norm_num)
  · have hδ0 : 0 < min (ε / 4) (1 / 2) := lt_min (by positivity) (by norm_num)
    have hδle : min (ε / 4) (1 / 2) ≤ ε / 4 := min_le_left _ _
    have hδhalf : min (ε / 4) (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hδsq : (min (ε / 4) (1 / 2)) ^ 2 ≤
        (min (ε / 4) (1 / 2)) * (1 / 2) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hδhalf hδ0.le
    nlinarith [hδle, hδsq, hε.le]

/-- Stage 5: literal height/log-volume comparison plus the main log-volume
estimate imply the additive height/weight bound. -/
theorem additiveHeightWeightBound_of_literalEstimates
    (height weight logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hweight_nonneg : ∀ a b c : Nat, 0 ≤ weight a b c)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat,
      height a b c ≤ (1 + δ) * logVolume a b c)
    (hmain : ∀ δ : ℝ, 0 < δ → ∃ D : ℝ,
      ∀ a b c : Nat,
        logVolume a b c ≤ (1 + δ) * weight a b c + hullVolume + D) :
    AdditiveHeightWeightBound height weight := by
  intro ε hε
  obtain ⟨δ, hδ0, hδsq⟩ := exists_delta_sq_le_one_add hε
  obtain ⟨D, hD⟩ := hmain δ hδ0
  refine ⟨(1 + δ) * (hullVolume + D), fun a b c => ?_⟩
  have h1 := hheight δ hδ0 a b c
  have h2 := hD a b c
  have hδnonneg : 0 ≤ 1 + δ := by linarith
  have hmul := mul_le_mul_of_nonneg_left h2 hδnonneg
  have hchain : height a b c ≤
      (1 + δ) * ((1 + δ) * weight a b c + hullVolume + D) :=
    le_trans h1 hmul
  have hw : 0 ≤ weight a b c := hweight_nonneg a b c
  have hcoef : (1 + δ) * ((1 + δ) * weight a b c + hullVolume + D) =
      (1 + δ) ^ 2 * weight a b c + (1 + δ) * (hullVolume + D) := by
    ring
  rw [hcoef] at hchain
  have hsqmul : (1 + δ) ^ 2 * weight a b c ≤
      (1 + ε) * weight a b c :=
    mul_le_mul_of_nonneg_right hδsq hw
  linarith


/-- Variant: the main log-volume estimate is already non-dilated. -/
theorem additiveHeightWeightBound_of_literalEstimates_nondilatedMain
    (height weight logVolume : Nat → Nat → Nat → ℝ) (hullVolume : ℝ)
    (hweight_nonneg : ∀ a b c : Nat, 0 ≤ weight a b c)
    (hheight : ∀ δ : ℝ, 0 < δ → ∀ a b c : Nat,
      height a b c ≤ (1 + δ) * logVolume a b c)
    (hmain : ∃ D : ℝ, ∀ a b c : Nat,
      logVolume a b c ≤ weight a b c + hullVolume + D) :
    AdditiveHeightWeightBound height weight := by
  intro ε hε
  obtain ⟨D, hD⟩ := hmain
  refine ⟨(1 + ε) * (hullVolume + D), fun a b c => ?_⟩
  have h1 := hheight ε hε a b c
  have h2 := hD a b c
  have hεnonneg : 0 ≤ 1 + ε := by linarith
  have hmul := mul_le_mul_of_nonneg_left h2 hεnonneg
  have hchain : height a b c ≤
      (1 + ε) * (weight a b c + hullVolume + D) :=
    le_trans h1 hmul
  have hcoef : (1 + ε) * (weight a b c + hullVolume + D) =
      (1 + ε) * weight a b c + (1 + ε) * (hullVolume + D) := by
    ring
  rw [hcoef] at hchain
  linarith

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVStage5NumericalCoreActual

end
