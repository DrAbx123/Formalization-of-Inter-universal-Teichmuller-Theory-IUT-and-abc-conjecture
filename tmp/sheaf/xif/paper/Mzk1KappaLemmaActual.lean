/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A763 R2: κ-lemma (pure real arithmetic, no lana dependency) -/

/- SSIneq in coefficient form: `(s - 1) * A <= V`, with `s = l(l+1)/12`, `A = log q/(2l)`.
The κ-relaxation is `(s - κ) * A <= V`.  Substituting gives the factorised form
  `(s - κ) * A = ((l+1)/24) * (1 - 12κ/(l(l+1))) * log q`.
Below: the exact factorisation and the implication to the relaxed bound. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual

/-- `s = l(l+1)/12` (the lattice coefficient). -/
def sL (l : ℝ) : ℝ := l * (l + 1) / 12

/-- `A = log q / (2l)`. -/
def AL (l logq : ℝ) : ℝ := logq / (2 * l)

/-- κ-relaxed SSIneq: `(s - κ) * A <= V`. -/
def SSIneqKappa (l logq κ V : ℝ) : Prop := (sL l - κ) * AL l logq ≤ V

/-- **κ-factorisation**: `(s - κ) * A = ((l+1)/24) * (1 - 12κ/(l(l+1))) * log q`. -/
theorem kappa_factor (l logq κ : ℝ) (hl : l ≠ 0) (hll : l * (l + 1) ≠ 0) :
    (sL l - κ) * AL l logq =
      ((l + 1) / 24) * (1 - 12 * κ / (l * (l + 1))) * logq := by
  unfold sL AL
  have hl1 : l + 1 ≠ 0 := by
    intro h
    apply hll
    rw [h, mul_zero]
  have h2l : 2 * l ≠ 0 := mul_ne_zero (by norm_num) hl
  field_simp [hl, hll, hl1, h2l]
  ring

/-- **R2 main**: from the κ-relaxed SSIneq one obtains the displayed explicit bound
`((l+1)/24) * (1 - 12κ/(l(l+1))) * log q <= V`. -/
theorem kappa_bound (l logq κ V : ℝ) (hl : l ≠ 0) (hll : l * (l + 1) ≠ 0)
    (h : SSIneqKappa l logq κ V) :
    ((l + 1) / 24) * (1 - 12 * κ / (l * (l + 1))) * logq ≤ V := by
  rw [← kappa_factor l logq κ hl hll]
  exact h

/-- The classical (κ = 1) instance. -/
theorem ssIneqKappa_one (l logq V : ℝ) (hl : l ≠ 0) (hll : l * (l + 1) ≠ 0)
    (h : SSIneqKappa l logq 1 V) :
    ((l + 1) / 24) * (1 - 12 / (l * (l + 1))) * logq ≤ V := by
  have hh := kappa_bound l logq 1 V hl hll h
  simpa using hh

end LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
