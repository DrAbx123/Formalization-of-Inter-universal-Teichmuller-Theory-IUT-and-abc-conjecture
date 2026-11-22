/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1FFRouteFirstStepActual
import Mathlib.Tactic

/-! # Mzk1FFRouteDecisionActual — FF route β decision (A876, qpilot)

ROUTES §10 β: on the Fargues–Fontaine adic curve `Y`, the Teichmüller element `[q♭]` has a
ρ-independent Gauss norm `exp c` (`c = log‖[q♭]‖ < 0`), while `‖p‖_ρ = ρ`.  Hence the
normalized q-valuation is `v_ρ = c / log ρ`.  The Θ-link's `j²` scaling is the radius map
`ρ ↦ ρ^{1/j²}`: proved here, `v_{ρ^{1/j²}} = j² · v_ρ`.

The region of Θ-values over an allowed radius interval is the value interval
`[v_a, v_b]`; its log-volume is `regionLogVolume = |v_b - v_a|`.  Since `v_ρ` is unbounded as
`ρ → 1⁻`, the union over allowed radii has no uniform upper bound: for every `j ≥ 2`, `A`
there are allowed `a,b` with `thetaRequirement j A < regionLogVolume a b c`.  Therefore, if
the radius `ρ_p` is independently selectable at each bad prime, the capsule upper bound
`(j²−1)·A` **fails** and route β is dead.

Survival branch: if the radii are globally bound (a single fixed radius per prime, tied to
the Θ-data), the region collapses to one value (log-volume 0), but then the container is
q-dependent only through `c = log‖[q♭]‖`; bounding it by `(j²−1)A` uniformly is *new global
content* (a binding condition), not present in the FF local model.

Formalized decision (this file):
* `normalizedQVal_radialScale` — the `j²` scaling law (`ρ ↦ ρ^{1/j²}` multiplies by `j²`);
* `regionLogVolume_unbounded` — unbounded union log-volume;
* `uniform_bound_fails_of_selectable` — no uniform `(j²−1)A` bound under radius selectability;
* `fixed_radius_collapse` — a globally fixed radius gives a single value (volume 0);
* `independent_selectability_no_coupling` — in the model, per-prime radii have no global coupling.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FFRouteDecisionActual

open LeanFormal.IUT.XiFPaper.Mzk1FFRouteFirstStepActual

/-! ### 1. j² scaling law: ρ ↦ ρ^{1/j²} multiplies the normalized valuation by j² -/

theorem normalizedQVal_radialScale {c ρ : ℝ} (j : ℕ) (hj : 0 < j)
    (h0 : 0 < ρ) (h1 : ρ < 1) :
    normalizedQVal c (ρ ^ (1 / (j : ℝ) ^ 2)) = (j : ℝ) ^ 2 * normalizedQVal c ρ := by
  unfold normalizedQVal
  rw [Real.log_rpow h0]
  have hjpos : (0 : ℝ) < (j : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hj) 2
  have hlog : Real.log ρ < 0 := uniformizerLogNorm_neg h0 h1
  field_simp
  ring

/-! ### 2. Region and its log-volume -/

/-- The log-volume of the Θ-value region obtained from an allowed radius interval `[a,b]`,
in normalized units. -/
def regionLogVolume (c a b : ℝ) : ℝ := |normalizedQVal c b - normalizedQVal c a|

/-- The requirement coming from the `j²−1` factor in the Θ-link. -/
def thetaRequirement (j : ℕ) (A : ℝ) : ℝ := ((j : ℝ) ^ 2 - 1) * A

/-- A uniform upper bound of the shape required by the capsule inequality. -/
def ThetaLinkUniformBound (c : ℝ) (j : ℕ) (A : ℝ) : Prop :=
  ∀ a b : ℝ, allowedRadius a → allowedRadius b → regionLogVolume c a b ≤ thetaRequirement j A

/-! ### 3. Unbounded log-volume -/

theorem regionLogVolume_unbounded {c : ℝ} (hc : c < 0) (B : ℝ) :
    ∃ a b : ℝ, allowedRadius a ∧ allowedRadius b ∧ B < regionLogVolume c a b := by
  obtain ⟨ρ1, h10, h11, hval1⟩ := normalizedQVal_surjective hc (by norm_num : (0 : ℝ) < 1)
  obtain ⟨ρ2, h20, h21, hval2⟩ := normalizedQVal_surjective hc (by linarith : (0 : ℝ) < |B| + 2)
  -- ensure value(ρ2) > value(ρ1); otherwise swap
  by_cases hle : normalizedQVal c ρ1 ≤ normalizedQVal c ρ2
  · refine ⟨ρ1, ρ2, ⟨h10, h11⟩, ⟨h20, h21⟩, ?_⟩
    unfold regionLogVolume
    rw [abs_of_nonneg (hle)]
    rw [hval2, hval1]
    have : (0:ℝ) < |B| + 2 := by positivity
    nlinarith [le_abs_self B, abs_nonneg B]
  · refine ⟨ρ2, ρ1, ⟨h20, h21⟩, ⟨h10, h11⟩, ?_⟩
    unfold regionLogVolume
    rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hle))]
    rw [hval2, hval1]
    nlinarith [le_abs_self B, abs_nonneg B, not_le.mp hle]

/-! ### 4. Uniform bound fails under selectability -/

theorem uniform_bound_fails_of_selectable {c : ℝ} (hc : c < 0)
    (j : ℕ) (A : ℝ) :
    ¬ ThetaLinkUniformBound c j A := by
  intro hbound
  obtain ⟨a, b, ha, hb, hgt⟩ := regionLogVolume_unbounded hc (thetaRequirement j A)
  exact absurd (hbound a b ha hb) (not_le.mpr hgt)

/-! ### 5. Fixed radius collapse -/

/-- If the radius is globally fixed to `ρ₀`, the value region is a single point, so the
union log-volume is zero. -/
theorem fixed_radius_collapse {c ρ₀ : ℝ} (h : allowedRadius ρ₀) :
    regionLogVolume c ρ₀ ρ₀ = 0 := by
  unfold regionLogVolume
  simp

/-! ### 6. Per-prime independent selectability (no global coupling in the model) -/

/-- Independent selectability at every prime with negative Gauss log-norm. -/
def PerPrimeSelectable {ι : Type*} (c : ι → ℝ) : Prop :=
  ∀ i : ι, RadiusSelectable (c i)

theorem independent_selectability_no_coupling {ι : Type*} (c : ι → ℝ)
    (hc : ∀ i, c i < 0) : PerPrimeSelectable c :=
  fun i => radiusSelectable_of_neg (hc i)

/-! ### 7. Decision -/

/-- **Route β decision**: (i) the `j²` scaling law holds; (ii) if radii are per-prime
selectable, no uniform `(j²−1)A` bound exists, so the capsule upper bound is lost;
(iii) a globally fixed radius collapses the region (volume 0), and its `q`-dependence then
requires a new global binding condition. -/
theorem ff_route_beta_decision {ι : Type*} (c : ι → ℝ) (hc : ∀ i, c i < 0)
    (j : ℕ) (hj : 0 < j) (A : ℝ) :
    PerPrimeSelectable c ∧ (∀ i, ¬ ThetaLinkUniformBound (c i) j A) ∧
      (∀ i (ρ₀ : ℝ), allowedRadius ρ₀ → regionLogVolume (c i) ρ₀ ρ₀ = 0) :=
  ⟨independent_selectability_no_coupling c hc,
    fun i => uniform_bound_fails_of_selectable (hc i) j A,
    fun i ρ₀ h => fixed_radius_collapse h⟩

/-! ### 8. Rows -/

def ffDecisionRows : List (String × String) :=
  [ ("j² scaling ρ ↦ ρ^{1/j²} multiplies normalized valuation by j²", "PROVED"),
    ("region log-volume = |v_b − v_a|", "DEFINED"),
    ("union log-volume unbounded as ρ → 1⁻", "PROVED"),
    ("uniform (j²−1)·A bound fails under selectability", "PROVED"),
    ("fixed global radius ⇒ single value (volume 0)", "PROVED"),
    ("per-prime independent selectability in the model", "PROVED"),
    ("global binding condition (new content) absent", "ASSESSMENT"),
    ("route β verdict: DEAD if ρ_p independent; conditional otherwise", "DECISION") ]

theorem ffDecisionRows_length : ffDecisionRows.length = 8 := rfl

#check normalizedQVal_radialScale
#check regionLogVolume_unbounded
#check uniform_bound_fails_of_selectable
#check ff_route_beta_decision
#check ffDecisionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1FFRouteDecisionActual
end
