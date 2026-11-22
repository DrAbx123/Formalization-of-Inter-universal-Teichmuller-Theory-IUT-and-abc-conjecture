/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1A763BoxAssemblyShaActual
import Mathlib.Tactic

/-! # A846 hull: procession average identities (L4)

With `n` capsules and paper label convention `j = 1..n`:
* `(1/n) Σ_{j=1}^n (j+1) = (n+3)/2`; at `l = 2n+1` this is `(l+5)/4`;
* `(1/n) Σ_{j=1}^n j² = (n+1)(2n+1)/6`; at `l = 2n+1` this is `l(l+1)/12`.

Both are proved here from `Finset.sum_range_id`/induction and green
`sum_sq_range` (`Mzk1A763BoxAssemblyShaActual`).  The convention used is
`j = 1..n` (so the linear term is `j+1`, shifted by 1); with the alternative
`j = 0..n-1` convention the linear average is `(n+1)/2`, not `(n+3)/2`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual

open LeanFormal.IUT.XiFPaper.Mzk1A763BoxAssemblyShaActual
open scoped BigOperators

/-- `Σ_{j=0}^{n-1} (j+2) = n(n+3)/2` (shifted linear sum, labels `1..n`). -/
theorem sum_range_add_two (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 2)) = (n : ℝ) * ((n : ℝ) + 3) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Linear average: `(1/n) Σ_{j=1}^n (j+1) = (n+3)/2`. -/
theorem avgJPlusOne_eq (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, ((j : ℝ) + 2)) =
      ((n : ℝ) + 3) / 2 := by
  rw [sum_range_add_two]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

/-- At `l = 2n+1`: the linear average is `(l+5)/4`. -/
theorem avgJPlusOne_eq_l (n : ℕ) (hn : 0 < n) (l : ℝ) (hl : l = 2 * (n : ℝ) + 1) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, ((j : ℝ) + 2)) = (l + 5) / 4 := by
  rw [avgJPlusOne_eq n hn, hl]
  ring

/-- Square average: `(1/n) Σ_{j=1}^n j² = (n+1)(2n+1)/6`. -/
theorem avgJSquare_eq (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2)) =
      ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  rw [sum_sq_range]
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']

/-- At `l = 2n+1`: the square average is `l(l+1)/12`. -/
theorem avgJSquare_eq_l (n : ℕ) (hn : 0 < n) (l : ℝ) (hl : l = 2 * (n : ℝ) + 1) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2)) =
      l * (l + 1) / 12 := by
  rw [avgJSquare_eq n hn, hl]
  ring

def avgRows : List (String × String × String) :=
  [ ("linear sum", "Σ_{j=0}^{n-1}(j+2) = n(n+3)/2", "PROVED (sum_range_add_two)"),
    ("linear average", "(1/n)Σ = (n+3)/2 = (l+5)/4 at l=2n+1", "PROVED (avgJPlusOne_eq / avgJPlusOne_eq_l)"),
    ("square sum", "Σ_{j=0}^{n-1}(j+1)^2 = n(n+1)(2n+1)/6", "GREEN (sum_sq_range)"),
    ("square average", "(1/n)Σ = (n+1)(2n+1)/6 = l(l+1)/12", "PROVED (avgJSquare_eq / avgJSquare_eq_l)"),
    ("convention", "j=1..n; alternative j=0..n-1 gives (n+1)/2 linear, not (l+5)/4", "CONVENTION"),
    ("L4 status", "both paper averages are now PROVED, not input", "CLOSED") ]

theorem avgRows_length : avgRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual.avgJPlusOne_eq_l
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual.avgJSquare_eq_l

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionAverageActual

end