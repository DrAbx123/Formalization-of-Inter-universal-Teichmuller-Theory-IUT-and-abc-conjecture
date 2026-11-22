import tmp.sheaf.xif.paper.Mzk1G1LocalHeightCriterionActual
import tmp.sheaf.xif.paper.Mzk1G1JHeightUniformActual
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1D1ProducerActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.G1KvCompactActual
open LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual
open LeanFormal.IUT.XiFPaper.G1QHeightActual

universe u

/-- Explicit sublinearity of the (D4) error term: for every eps > 0 there is a
threshold H such that for all h >= H,
  C * sqrt h * log (2 C h) <= eps * h.
This is the real-analytic input needed for the section 6.4 error absorption; it
is proved here from the elementary estimate log x <= 4 x^(1/4). -/
theorem sqrt_mul_log_sublinear {C : ℝ} (hC : 0 ≤ C) :
    ∀ ε : ℝ, 0 < ε → ∃ H : ℝ, ∀ h : ℝ, H ≤ h →
      C * Real.sqrt h * Real.log (2 * C * h) ≤ ε * h := by
  intro ε hε
  rcases lt_or_eq_of_le hC with hCpos | h0C
  · set σ : ℝ := Real.sqrt (Real.sqrt (2 * C)) with hσ
    have h2Cnn : 0 ≤ 2 * C := by positivity
    have h2Cpos : 0 < 2 * C := by positivity
    have hσnn : 0 ≤ σ := Real.sqrt_nonneg _
    set K0 : ℝ := 4 * C * σ / ε with hK0
    have hK0nn : 0 ≤ K0 := by
      rw [hK0]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hCpos.le) hσnn) hε.le
    refine ⟨max 1 (K0 ^ 4), ?_⟩
    intro h hh
    have h1 : 1 ≤ h := le_trans (le_max_left 1 (K0 ^ 4)) hh
    have h2 : K0 ^ 4 ≤ h := le_trans (le_max_right 1 (K0 ^ 4)) hh
    have hhnn : 0 ≤ h := le_trans zero_le_one h1
    have hhpos : 0 < h := lt_of_lt_of_le zero_lt_one h1
    -- the fourth root of h, written as an iterated square root
    set u : ℝ := Real.sqrt (Real.sqrt h) with hu
    have hu2 : u ^ 2 = Real.sqrt h := by
      rw [hu]
      exact Real.sq_sqrt (Real.sqrt_nonneg h)
    have hu4 : u ^ 4 = h := by
      have h4 : u ^ 4 = (Real.sqrt h) ^ 2 := by
        rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu2]
      rw [h4, Real.sq_sqrt hhnn]
    have hsqrt1 : K0 ^ 2 ≤ Real.sqrt h := by
      have hA := Real.sqrt_le_sqrt h2
      rwa [show Real.sqrt (K0 ^ 4) = K0 ^ 2 by
        rw [show K0 ^ 4 = (K0 ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]] at hA
    have huK : K0 ≤ u := by
      have hB := Real.sqrt_le_sqrt hsqrt1
      rwa [show Real.sqrt (K0 ^ 2) = K0 by rw [Real.sqrt_sq hK0nn]] at hB
    have h4root_twoC : (2 * C) ^ (1 / 4 : ℝ) = σ := by
      have hsq : Real.sqrt (Real.sqrt (2 * C)) = (2 * C) ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul h2Cnn]
        norm_num
      rw [hσ, ← hsq]
    have h4root_h : h ^ (1 / 4 : ℝ) = u := by
      have hsq : Real.sqrt (Real.sqrt h) = h ^ (1 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hhnn]
        norm_num
      rw [hu, ← hsq]
    -- log(2 C h) <= 4 (2 C h)^(1/4) = 4 sigma u
    have hlog : Real.log (2 * C * h) ≤ 4 * (2 * C * h) ^ (1 / 4 : ℝ) := by
      have hL : Real.log (2 * C * h) ≤ (2 * C * h) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) :=
        Real.log_le_rpow_div (mul_nonneg h2Cnn hhnn) (by norm_num)
      calc Real.log (2 * C * h) ≤ (2 * C * h) ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) := hL
        _ = 4 * (2 * C * h) ^ (1 / 4 : ℝ) := by
            rw [div_eq_mul_inv, show ((1 / 4 : ℝ)⁻¹) = 4 by norm_num]
            ring
    have hlog2 : Real.log (2 * C * h) ≤ 4 * σ * u := by
      calc Real.log (2 * C * h) ≤ 4 * (2 * C * h) ^ (1 / 4 : ℝ) := hlog
        _ = 4 * ((2 * C) ^ (1 / 4 : ℝ) * h ^ (1 / 4 : ℝ)) := by
            rw [Real.mul_rpow h2Cnn hhnn]
        _ = 4 * (σ * u) := by rw [h4root_twoC, h4root_h]
        _ = 4 * σ * u := by ring
    have hbound1 : C * Real.sqrt h * Real.log (2 * C * h) ≤
        C * Real.sqrt h * (4 * σ * u) :=
      mul_le_mul_of_nonneg_left hlog2
        (mul_nonneg hCpos.le (Real.sqrt_nonneg h))
    have hun : 0 ≤ u := by
      rw [hu]
      exact Real.sqrt_nonneg _
    have hu3nn : 0 ≤ u ^ 3 := pow_nonneg hun 3
    have hstep : C * Real.sqrt h * (4 * σ * u) = 4 * C * σ * u ^ 3 := by
      rw [← hu2]
      ring
    have hmain : 4 * C * σ * u ^ 3 ≤ ε * h := by
      have hmul : K0 * u ^ 3 ≤ u * u ^ 3 := mul_le_mul_of_nonneg_right huK hu3nn
      have hu4' : u * u ^ 3 = u ^ 4 := by ring
      have h4Cσ : 4 * C * σ = ε * K0 := by
        rw [hK0]
        field_simp [ne_of_gt hε]
      calc 4 * C * σ * u ^ 3 = ε * (K0 * u ^ 3) := by
            rw [h4Cσ]; ring
        _ ≤ ε * (u * u ^ 3) := mul_le_mul_of_nonneg_left hmul hε.le
        _ = ε * u ^ 4 := by rw [hu4']
        _ = ε * h := by rw [hu4]
    calc C * Real.sqrt h * Real.log (2 * C * h) ≤ C * Real.sqrt h * (4 * σ * u) := hbound1
      _ = 4 * C * σ * u ^ 3 := hstep
      _ ≤ ε * h := hmain
  · -- C = 0
    have hC0 : C = 0 := h0C.symm
    refine ⟨0, ?_⟩
    intro h hh
    have hhnn : 0 ≤ h := le_trans (le_of_eq rfl) hh
    have hL : C * Real.sqrt h * Real.log (2 * C * h) = 0 := by
      rw [hC0]; ring
    rw [hL]
    exact mul_nonneg hε.le hhnn

/-- The analytic input to the error absorption of route section 6.4, after
de-conditionalizing (D3): the q-height of the initial Theta-data is the actual
j-height `jHeight`, so the height dictionary (D3) is no longer a field but the
theorem `height_dictionary_deg`.  What remains is the operational form (D4) of
the independent upper bound of section 5, whose constants may depend on the
degree bound `d`. -/
structure D1AnalyticInput (D : KvData) (d : ℕ) where
  /-- The constant C_d of (D4), depending only on the degree bound. -/
  Cd : ℝ
  hCd : 0 ≤ Cd
  /-- The constant C_K of (D4). -/
  CK : ℝ
  /-- (D4) the operational form of the section 5 upper bound, with the actual
  j-height as q-height. -/
  upper_estimate : ∀ (K : Type u) [Field K] [NumberField K] (lam : K),
    Module.finrank ℚ K ≤ d → InKv D lam →
      jHeight lam / 6 ≤
        (1 + Cd / Real.sqrt (jHeight lam)) *
            (discOver K + truncConductor lam) +
          Cd * Real.sqrt (jHeight lam) *
            Real.log (2 * Cd * jHeight lam) + CK

/-- The elementary ratio estimate at the heart of the absorption: for
0 < mu <= 1 one has (1 + mu/6)/(1 - mu/4) <= 1 + mu. -/
theorem ratio_le {μ : ℝ} (h0 : 0 < μ) (h1 : μ ≤ 1) :
    (1 + μ / 6) / (1 - μ / 4) ≤ 1 + μ := by
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - μ / 4)]
  nlinarith [mul_nonneg h0.le (by linarith : (0 : ℝ) ≤ 7 - 3 * μ)]

/-- Route section 6.4: from the actual height dictionary (D3) of
`height_dictionary_deg`, the section 5 upper bound in the operational form
(D4), and the explicit sublinearity of the error, derive the actual local height
criterion D1.  The quantifiers of D1 are those of
the route: for fixed d, K_V and eta the constant C is produced, and it is
independent of lam. -/
theorem d1_of_analyticInput {d : ℕ} {D : KvData} (A : D1AnalyticInput.{u} D d)
    {η : ℝ} (hη : 0 < η) : LocalHeightCriterion.{u} d D η := by
  classical
  obtain ⟨B, hB⟩ := G1JHeightUniformActual.height_dictionary_deg d
  set μ : ℝ := min η 1 with hμdef
  have hμpos : 0 < μ := lt_min hη zero_lt_one
  have hμη : μ ≤ η := min_le_left _ _
  have hμ1 : μ ≤ 1 := min_le_right _ _
  obtain ⟨H1, hH1⟩ := sqrt_mul_log_sublinear A.hCd (μ / 24) (by positivity)
  set H2 : ℝ := (6 * A.Cd / μ) ^ 2 with hH2def
  have hH2nn : 0 ≤ 6 * A.Cd / μ := by
    apply div_nonneg
    · exact mul_nonneg (by norm_num) A.hCd
    · exact hμpos.le
  set H : ℝ := max 1 (max H1 H2) with hHdef
  have hH1le : H1 ≤ H := le_trans (le_max_left H1 H2) (le_max_right 1 (max H1 H2))
  have hH2le : H2 ≤ H := le_trans (le_max_right H1 H2) (le_max_right 1 (max H1 H2))
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_left 1 (max H1 H2))
  have hden : 0 < 1 - μ / 4 := by linarith
  set Kc : ℝ := ((μ / 4) * B + A.CK + B) / (1 - μ / 4) with hKc
  refine ⟨max (H / 6 + B) (max 0 Kc), ?_⟩
  intro K _ _ hdeg lam hlam
  have hD3 : |Height.logHeight₁ lam - jHeight lam / 6| ≤ B := hB (K := K) hdeg lam
  have hD4 := A.upper_estimate K lam hdeg hlam
  have hdN : 0 ≤ discOver K + truncConductor lam :=
    add_nonneg (discOver_nonneg K) (truncConductor_nonneg lam)
  have hlow : Height.logHeight₁ lam - jHeight lam / 6 ≤ B := (abs_le.mp hD3).2
  have hhigh : jHeight lam / 6 - Height.logHeight₁ lam ≤ B := by
    have := (abs_le.mp hD3).1
    linarith
  have hLq : Height.logHeight₁ lam ≤ jHeight lam / 6 + B := by linarith
  have hqL : jHeight lam ≤ 6 * Height.logHeight₁ lam + 6 * B := by linarith
  by_cases hlarge : H ≤ jHeight lam
  · have hqpos : 0 < jHeight lam := lt_of_lt_of_le hHpos hlarge
    have herr : A.Cd * Real.sqrt (jHeight lam) *
        Real.log (2 * A.Cd * jHeight lam) ≤ (μ / 24) * jHeight lam :=
      hH1 _ (le_trans hH1le hlarge)
    have hs2 : Real.sqrt H2 = 6 * A.Cd / μ := by
      rw [hH2def, Real.sqrt_sq_eq_abs, abs_of_nonneg hH2nn]
    have hsq : 6 * A.Cd / μ ≤ Real.sqrt (jHeight lam) := by
      calc 6 * A.Cd / μ = Real.sqrt H2 := hs2.symm
        _ ≤ Real.sqrt (jHeight lam) := Real.sqrt_le_sqrt (le_trans hH2le hlarge)
    have hsqrt : A.Cd / Real.sqrt (jHeight lam) ≤ μ / 6 := by
      by_cases hCd0 : A.Cd = 0
      · rw [hCd0, zero_div]
        positivity
      · have hCdpos : 0 < A.Cd := lt_of_le_of_ne A.hCd (Ne.symm hCd0)
        have hdenpos : 0 < 6 * A.Cd / μ := by positivity
        have hstep1 : A.Cd / Real.sqrt (jHeight lam) ≤ A.Cd / (6 * A.Cd / μ) :=
          div_le_div_of_nonneg_left A.hCd hdenpos hsq
        have hstep2 : A.Cd / (6 * A.Cd / μ) = μ / 6 := by
          field_simp [hCd0, ne_of_gt hμpos]
        linarith
    have hmul : (A.Cd / Real.sqrt (jHeight lam)) *
        (discOver K + truncConductor lam) ≤
        (μ / 6) * (discOver K + truncConductor lam) :=
      mul_le_mul_of_nonneg_right hsqrt hdN
    have hq6 : jHeight lam / 6 ≤
        (1 + μ / 6) * (discOver K + truncConductor lam) +
          A.Cd * Real.sqrt (jHeight lam) *
            Real.log (2 * A.Cd * jHeight lam) + A.CK := by
      nlinarith [hD4, hmul]
    have hmulq : (μ / 24) * (jHeight lam) ≤
        (μ / 4) * Height.logHeight₁ lam + (μ / 4) * B := by
      have h1 : (μ / 24) * (jHeight lam) ≤
          (μ / 24) * (6 * Height.logHeight₁ lam + 6 * B) :=
        mul_le_mul_of_nonneg_left hqL (by positivity)
      have h2 : (μ / 24) * (6 * Height.logHeight₁ lam + 6 * B) =
          (μ / 4) * Height.logHeight₁ lam + (μ / 4) * B := by ring
      linarith
    have hstep : Height.logHeight₁ lam ≤
        (1 + μ / 6) * (discOver K + truncConductor lam) +
          (μ / 24) * (jHeight lam) + A.CK + B := by
      linarith [hLq, hq6, herr]
    have hstep2 : Height.logHeight₁ lam ≤
        (1 + μ / 6) * (discOver K + truncConductor lam) +
          (μ / 4) * Height.logHeight₁ lam + (μ / 4) * B + A.CK + B := by
      linarith [hstep, hmulq]
    have hkey : (1 - μ / 4) * Height.logHeight₁ lam ≤
        (1 + μ / 6) * (discOver K + truncConductor lam) +
          ((μ / 4) * B + A.CK + B) := by
      linarith [hstep2]
    have hLbound : Height.logHeight₁ lam ≤
        ((1 + μ / 6) / (1 - μ / 4)) * (discOver K + truncConductor lam) + Kc := by
      have h1 : Height.logHeight₁ lam ≤
          ((1 + μ / 6) * (discOver K + truncConductor lam) +
            ((μ / 4) * B + A.CK + B)) / (1 - μ / 4) := by
        rw [le_div_iff₀ hden]
        linarith [hkey]
      have h2 : ((1 + μ / 6) * (discOver K + truncConductor lam) +
            ((μ / 4) * B + A.CK + B)) / (1 - μ / 4) =
          ((1 + μ / 6) / (1 - μ / 4)) * (discOver K + truncConductor lam) + Kc := by
        rw [hKc]
        field_simp [ne_of_gt hden]
      linarith
    have hratio := ratio_le hμpos hμ1
    have hcoef : ((1 + μ / 6) / (1 - μ / 4)) *
        (discOver K + truncConductor lam) ≤
        (1 + μ) * (discOver K + truncConductor lam) :=
      mul_le_mul_of_nonneg_right hratio hdN
    have hKcle : Kc ≤ max 0 Kc := le_max_right 0 Kc
    have hcoef2 : (1 + μ) * (discOver K + truncConductor lam) ≤
        (1 + η) * (discOver K + truncConductor lam) := by
      apply mul_le_mul_of_nonneg_right _ hdN
      linarith
    calc Height.logHeight₁ lam ≤
          ((1 + μ / 6) / (1 - μ / 4)) * (discOver K + truncConductor lam) + Kc := hLbound
      _ ≤ (1 + μ) * (discOver K + truncConductor lam) + max 0 Kc := by linarith
      _ ≤ (1 + η) * (discOver K + truncConductor lam) +
            max (H / 6 + B) (max 0 Kc) := by
          have hle : max 0 Kc ≤ max (H / 6 + B) (max 0 Kc) := le_max_right _ _
          linarith [hcoef2]
  · push_neg at hlarge
    have hsmall : Height.logHeight₁ lam ≤ H / 6 + B := by linarith
    have hmax1 : H / 6 + B ≤ max (H / 6 + B) (max 0 Kc) := le_max_left _ _
    have hnonneg : 0 ≤ (1 + η) * (discOver K + truncConductor lam) := by
      apply mul_nonneg (by linarith) hdN
    calc Height.logHeight₁ lam ≤ H / 6 + B := hsmall
      _ ≤ max (H / 6 + B) (max 0 Kc) := hmax1
      _ ≤ (1 + η) * (discOver K + truncConductor lam) +
            max (H / 6 + B) (max 0 Kc) := by linarith

#print axioms sqrt_mul_log_sublinear
#print axioms ratio_le
#print axioms d1_of_analyticInput

end LeanFormal.IUT.XiFPaper.G1D1ProducerActual
end