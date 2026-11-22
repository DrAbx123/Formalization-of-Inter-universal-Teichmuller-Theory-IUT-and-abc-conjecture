import tmp.sheaf.xif.paper.Mzk1G1BelyiActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial

/-- Actual Belyi polynomial c_n X^2 with c_n = 1/(n+2). -/
def belyiAllCompactPoly (n : ℕ) : ℚ[X] :=
  C ((n + 2 : ℚ)⁻¹) * X ^ 2

/-- Actual Belyi map parameterized by the curve coefficient c_n. -/
def belyiAllCompactMap (n : ℕ) : BelyiMapData ℚ where
  poly := belyiAllCompactPoly n
  degree_pos := by
    have h : (belyiAllCompactPoly n).natDegree = 2 := by
      unfold belyiAllCompactPoly
      compute_degree!
    rw [h]
    norm_num
  ramified_only_base := by
    intro x hx
    have hder : (belyiAllCompactPoly n).derivative.eval x =
        (2 * (n + 2 : ℚ)⁻¹) * x := by
      unfold belyiAllCompactPoly
      simp [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring_nf
    rw [hder] at hx
    have hcoef : (2 * (n + 2 : ℚ)⁻¹) ≠ 0 := by
      have h : (n + 2 : ℚ) ≠ 0 := by positivity
      exact mul_ne_zero (by norm_num) (inv_ne_zero h)
    have hx0 : x = 0 := (mul_eq_zero.mp hx).resolve_left hcoef
    left
    subst x
    simp [belyiAllCompactPoly]

/-- Actual sequence of values. -/
def belyiAllCompactSequence : ℕ → ℚ → ℚ :=
  fun n x => (belyiAllCompactMap n).poly.eval x

/-- Actual all-compact uniform epsilon criterion. -/
def UniformEpsilonCriterionRatAll (f : ℕ → ℚ → ℚ) : Prop :=
  ∀ K : Set ℚ, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ K, |(f n x : ℝ)| < ε

/-- Actual all-compact uniform epsilon for the nontrivial Belyi family. -/
theorem belyiAllCompactSequence_uniformEpsilon :
    UniformEpsilonCriterionRatAll belyiAllCompactSequence := by
  intro K hK ε hε
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℚ)).mp hK.isBounded
  let C : ℝ := max R 0
  have hC : ∀ x ∈ K, |((x : ℚ) : ℝ)| ≤ C := by
    intro x hx
    have hxd : dist x (0 : ℚ) ≤ R := hR hx
    rw [dist_eq_norm, sub_zero, ← Rat.norm_cast_real, Real.norm_eq_abs] at hxd
    exact hxd.trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_max_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (C ^ 2 / ε)
  refine ⟨N, fun n hn x hx => ?_⟩
  have hxabs : |((x : ℚ) : ℝ)| ≤ C := hC x hx
  have hx2 : |(((x : ℚ) : ℝ) ^ 2)| ≤ C ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), sq_le_sq]
    simpa [abs_of_nonneg hC0] using hxabs
  have hval : |((belyiAllCompactSequence n x : ℚ) : ℝ)| =
      (1 / ((n : ℝ) + 2)) * |(((x : ℚ) : ℝ) ^ 2)| := by
    simp [belyiAllCompactSequence, belyiAllCompactMap, belyiAllCompactPoly,
      abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((n : ℝ) + 2)⁻¹)]
  rw [hval]
  have hden : (0:ℝ) < (n : ℝ) + 2 := by positivity
  have hle : (1 / ((n : ℝ) + 2)) * |(((x : ℚ) : ℝ) ^ 2)| ≤
      1 / ((n : ℝ) + 2) * C ^ 2 :=
    mul_le_mul_of_nonneg_left hx2 (by positivity)
  have hlt : (1 / ((n : ℝ) + 2)) * C ^ 2 < ε := by
    have hNle : C ^ 2 / ε < (n : ℝ) := by
      have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hmul : C ^ 2 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hNle
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  exact lt_of_le_of_lt hle hlt

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
