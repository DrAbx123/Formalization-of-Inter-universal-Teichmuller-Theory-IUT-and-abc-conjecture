import tmp.sheaf.xif.paper.Mzk1G1BelyiActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial

/-- Actual degree-n Belyi polynomial X^(n+2), ramified only at 0 and ∞. -/
def belyiDegreePoly (n : ℕ) : ℚ[X] := X ^ (n + 2)

/-- The actual Belyi map of degree n+2. -/
def belyiDegreeMap (n : ℕ) : BelyiMapData ℚ where
  poly := belyiDegreePoly n
  degree_pos := by
    have h : (belyiDegreePoly n).natDegree = n + 2 := by
      unfold belyiDegreePoly
      compute_degree!
    rw [h]
    omega
  ramified_only_base := by
    intro x hx
    have hder : (belyiDegreePoly n).derivative.eval x =
        (n + 2 : ℚ) * x ^ (n + 1) := by
      unfold belyiDegreePoly
      simp [Polynomial.derivative_X_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring_nf
      left
      trivial
    rw [hder] at hx
    have hcoef : (n + 2 : ℚ) ≠ 0 := by positivity
    have hx0 : x = 0 := by
      exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp
        ((mul_eq_zero.mp hx).resolve_left hcoef)
    left
    subst x
    simp [belyiDegreePoly]

/-- Actual infinite Belyi family parameterized by degree. -/
def belyiDegreeFamily : ℕ → BelyiMapData ℚ := belyiDegreeMap

/-- Actual sequence of values of the degree family. -/
def belyiDegreeSequence : ℕ → ℚ → ℚ :=
  fun n x => (belyiDegreeFamily n).poly.eval x

/-- Uniform epsilon criterion on the half-unit ball. -/
def UniformEpsilonCriterionRatUnit (f : ℕ → ℚ → ℚ) : Prop :=
  ∀ K : Set ℚ, K ⊆ Metric.closedBall (0 : ℚ) (1 / 2) → IsCompact K →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ K, |(f n x : ℝ)| < ε

/-- Actual nontrivial Belyi family sequence converges uniformly to 0 on the
half-unit ball. -/
theorem belyiDegreeSequence_uniformEpsilon :
    UniformEpsilonCriterionRatUnit belyiDegreeSequence := by
  intro K hKsub hK ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N + 2, fun n hn x hx => ?_⟩
  have hxabs : |((x : ℚ) : ℝ)| ≤ 1 / 2 := by
    have hxball : dist x (0 : ℚ) ≤ (1 / 2 : ℝ) := hKsub hx
    rw [dist_eq_norm, sub_zero, ← Rat.norm_cast_real, Real.norm_eq_abs] at hxball
    exact hxball
  have hval : |((belyiDegreeSequence n x : ℚ) : ℝ)| =
      |((x : ℚ) : ℝ)| ^ (n + 2) := by
    simp [belyiDegreeSequence, belyiDegreeFamily, belyiDegreeMap, belyiDegreePoly,
      abs_pow]
  rw [hval]
  have hbound : |((x : ℚ) : ℝ)| ^ (n + 2) ≤ (1 / 2 : ℝ) ^ (n + 2) :=
    pow_le_pow_left₀ (abs_nonneg _) hxabs _
  have hNle : (1 / 2 : ℝ) ^ (n + 2) ≤ (1 / 2 : ℝ) ^ N := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    omega
  exact lt_of_le_of_lt (hbound.trans hNle) hN

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
