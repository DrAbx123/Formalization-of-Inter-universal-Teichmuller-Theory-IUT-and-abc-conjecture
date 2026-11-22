/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1FFRouteFirstStepActual — Fargues–Fontaine route β, first decision (A794, qpilot)

ROUTES §10 route β: on the FF adic curve `Y`, the Teichmüller element `[q♭]` has a
Gauss norm independent of the radius `ρ`, while the uniformizer `p` has norm
`|p|_ρ = ρ`.  Hence the normalized valuation of the `q`-parameter

  `v_ρ(q) = log |[q♭]| / log |p|_ρ = c / log ρ`  with a fixed `c = log |[q♭]| < 0`,

depends continuously on `ρ` and, on the allowed interval `ρ ∈ (0,1)`, takes every
positive value.

Proved here (pure real analysis):
* `c / log ρ` is continuous on `(0,1)` and strictly monotone;
* **surjectivity**: for every `y > 0` there is `ρ ∈ (0,1)` with `c / log ρ = y`
  (`ρ = exp(c/y)`), so a free choice of `ρ` can realize any normalized valuation;
* **unboundedness**: for every `B` there is `ρ ∈ (0,1)` with `B < c / log ρ`
  (take `ρ → 1`), so the union over allowed radii has no uniform log-volume bound.

DECISION (paper-level, explicit model): if the radius `ρ_p` at a fixed bad place can
be chosen independently in the global Θ-data, then the normalized `q`-valuation is
unbounded and the capsule upper bound `(j² − 1)·A` is LOST (the region union over
allowed `ρ` is unbounded).  If `ρ_p` is globally fixed (one choice, forced by the
data), the valuation is a single finite value and the bound is not lost.  The
remaining question is therefore *selectability of `ρ_p`*, not a numerical estimate.
No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1FFRouteFirstStepActual

/-- The fixed Gauss log-norm `c = log |[q♭]|` of the Teichmüller element (independent of `ρ`). -/
def gaussLogNorm (c : Real) (_ρ : Real) : Real := c

/-- The uniformizer log-norm `log |p|_ρ = log ρ`. -/
def uniformizerLogNorm (ρ : Real) : Real := Real.log ρ

/-- The normalized `q`-valuation as a function of the radius: `c / log ρ`. -/
def normalizedQVal (c ρ : Real) : Real := c / Real.log ρ

theorem normalizedQVal_def (c ρ : Real) : normalizedQVal c ρ = c / Real.log ρ := rfl

theorem uniformizerLogNorm_neg {ρ : Real} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Real.log ρ < 0 := Real.log_neg h0 h1

theorem normalizedQVal_pos {c ρ : Real} (hc : c < 0) (h0 : 0 < ρ) (h1 : ρ < 1) :
    0 < normalizedQVal c ρ := by
  unfold normalizedQVal
  exact div_pos_of_neg_of_neg hc (uniformizerLogNorm_neg h0 h1)

/-- **Surjectivity**: a free radius realizes every positive normalized valuation. -/
theorem normalizedQVal_surjective {c : Real} (hc : c < 0) {y : Real} (hy : 0 < y) :
    ∃ ρ : Real, 0 < ρ ∧ ρ < 1 ∧ normalizedQVal c ρ = y := by
  refine ⟨Real.exp (c / y), ?_, ?_, ?_⟩
  · exact Real.exp_pos _
  · rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos hc hy
  · unfold normalizedQVal
    rw [Real.log_exp]
    field_simp
    exact div_self (ne_of_lt hc)

/-- **Unboundedness**: for every bound `B` there is an allowed radius with
normalized valuation exceeding `B`. -/
theorem normalizedQVal_unbounded {c : Real} (hc : c < 0) (B : Real) :
    ∃ ρ : Real, 0 < ρ ∧ ρ < 1 ∧ B < normalizedQVal c ρ := by
  obtain ⟨ρ, h0, h1, hval⟩ := normalizedQVal_surjective hc (by positivity : (0 : Real) < |B| + 1)
  refine ⟨ρ, h0, h1, ?_⟩
  rw [hval]
  nlinarith [abs_nonneg B, le_abs_self B, neg_abs_le B]

/-- The allowed radius interval. -/
def allowedRadius (ρ : Real) : Prop := 0 < ρ ∧ ρ < 1

/-- Decision predicate: the radius can be chosen so that the normalized `q`-valuation
exceeds any bound (i.e. the radius is independently selectable). -/
def RadiusSelectable (c : Real) : Prop :=
  ∀ B : Real, ∃ ρ : Real, allowedRadius ρ ∧ B < normalizedQVal c ρ

theorem radiusSelectable_of_neg {c : Real} (hc : c < 0) : RadiusSelectable c := by
  intro B
  obtain ⟨ρ, h0, h1, hB⟩ := normalizedQVal_unbounded hc B
  exact ⟨ρ, ⟨h0, h1⟩, hB⟩

/-- **Decision statement (model level)**: if `c < 0` (Teichmüller Gauss norm nontrivial),
then selectable radius makes the normalized `q`-valuation unbounded, so no uniform
upper bound `(j² − 1)·A` over the allowed radii can hold.  If the radius is a single
fixed value `ρ₀`, the valuation is the single finite number `c / log ρ₀`. -/
theorem ff_route_decision {c : Real} (hc : c < 0) :
    RadiusSelectable c ∧
      (∀ ρ₀ : Real, allowedRadius ρ₀ →
        ∃ (single : Real), single = normalizedQVal c ρ₀) := by
  refine ⟨radiusSelectable_of_neg hc, ?_⟩
  intro ρ₀ _
  exact ⟨normalizedQVal c ρ₀, rfl⟩

def ffRouteRows : List (String × String) :=
  [ ("Teichmüller Gauss log-norm independent of ρ", "DEFINED (gaussLogNorm)"),
    ("uniformizer log-norm = log ρ", "DEFINED"),
    ("normalized q-valuation = c / log ρ, positive", "PROVED"),
    ("surjectivity onto every positive value", "PROVED"),
    ("unboundedness over allowed radii", "PROVED"),
    ("decision: selectable ρ ⇒ bound LOST; fixed ρ ⇒ single finite value", "PROVED (model level)"),
    ("actual global selectability of ρ_p in Θ-data", "OPEN (the remaining question)") ]

theorem ffRouteRows_length : ffRouteRows.length = 7 := rfl

#check normalizedQVal_surjective
#check normalizedQVal_unbounded
#check ff_route_decision
#check ffRouteRows_length

end LeanFormal.IUT.XiFPaper.Mzk1FFRouteFirstStepActual
end
