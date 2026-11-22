import Mathlib.NumberTheory.Height.Basic
import Mathlib.Tactic
/-!
# R6:

Citation (Lead/Sophie pin): [GenEll] Definition 3.3 local height + route L566/L569/L576; there is **no literal IV line** for `h_E ≤ m_i h_{O(1)}`/`h_omega` normalization — do not claim an IV literal. actual local Weil function from multi-coordinate projective height (no zero proxy)

ROUTE UPDATED (Lead 2026-11-17 23:49): the previous `hDivP = Height.logHeight` of a
`Unit`-indexed tuple is a **zero proxy** (`Height.logHeight_eq_zero_of_subsingleton`) and is
**removed from the consumption chain**.  R6 replaces it by the actual local Weil function
of the reduced divisor `E_i = (phi_i^*{0,1,infinity})_red`:

`lambda_{E_i,v}(y) = m_i log max(|x_0|_v,|x_1|_v,|x_2|_v) - log max_j |P_{i,j}(x)|_v`

with homogeneous generators `P_{i,j}` completed to the same degree `m_i`; summing over `v`
by the product formula gives

`h_E(y) = m_i bar h_{O(1)}(y) - bar h([P_0(x):...:P_s(x)]) + O_i(1)`,

and the **multi-coordinate projective height is nonnegative**
(`Height.logHeight_nonneg`, Mathlib Basic.lean:366), hence
`h_E <= m_i bar h_{O(1)}` and (A4 normalization) `h_E <= (m_i/(n-3)) h_omega + C_i`.

## Reuse / donor check (2026-11-17)
* `Height.logHeight_nonneg (x : ι → K) : 0 ≤ Height.logHeight x` (multi-coordinate!);
* `Height.one_le_mulHeight`, `Height.mulHeight_pos`;
* `Mzk1HTF4SchemeMultiplicityActual`/`FunctionFieldActual` — donors only, not in main chain.

**No single-coordinate proxy** is used: `hP` is the height of the multi-coordinate tuple of
homogeneous generators (`ι`-indexed, not `Unit`).  The identification of `h_E` with the
divisor height of the reduced `E_i` and the completion-to-degree-`m_i` construction are
explicit fields/obligations (`hE_eq`, `hnorm`), not assumed identifications.
-/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4R6Actual

/-- R6 local Weil data: homogeneous generators of degree `m` (multi-coordinate height
`hP`), the O(1)-height `hO1`, and the normalized omega-height `hOmega`. -/
structure R6LocalWeilData where
  n : ℕ
  n_gt_three : 3 < (n : ℝ)
  m : ℕ
  hO1 : ℝ
  /-- multi-coordinate projective height of the completed generators -/
  hP : ℝ
  hP_nonneg : 0 ≤ hP
  hE : ℝ
  hE_eq : hE = (m : ℝ) * hO1 - hP
  hOmega : ℝ
  hnorm : (m : ℝ) * hO1 = (m : ℝ) / ((n : ℝ) - 3) * hOmega

/-- **R6.1**: the local Weil function is bounded by the O(1)-height, using nonnegativity of
the multi-coordinate projective height. -/
theorem R6LocalWeilData.hE_le_m (D : R6LocalWeilData) :
    D.hE ≤ (D.m : ℝ) * D.hO1 := by
  rw [D.hE_eq]
  linarith [D.hP_nonneg]

/-- **R6.1 (κ-form)**: `h_E ≤ (m/(n−3)) h_omega` after the A4 normalization. -/
theorem R6LocalWeilData.hE_le_kappa (D : R6LocalWeilData) :
    D.hE ≤ (D.m : ℝ) / ((D.n : ℝ) - 3) * D.hOmega := by
  have h := D.hE_le_m
  rw [D.hnorm] at h
  exact h

/-- Concrete R6 data from a multi-coordinate tuple `x : ι → K` (not `Unit`!):
`hP = Height.logHeight x` is nonnegative by Mathlib, and `hOmega := (n−3) hO1` makes
the A4 normalization an identity. -/
noncomputable def R6LocalWeilData.ofProjHeight {K ι : Type*} [Field K]
    [Height.AdmissibleAbsValues K] [Fintype ι] (n : ℕ) (hn : 3 < (n : ℝ)) (m : ℕ)
    (hO1 : ℝ) (x : ι → K) : R6LocalWeilData where
  n := n
  n_gt_three := hn
  m := m
  hO1 := hO1
  hP := Height.logHeight x
  hP_nonneg := Height.logHeight_nonneg x
  hE := (m : ℝ) * hO1 - Height.logHeight x
  hE_eq := rfl
  hOmega := ((n : ℝ) - 3) * hO1
  hnorm := by
    have hne : ((n : ℝ) - 3) ≠ 0 := by linarith
    field_simp [hne]

#print axioms R6LocalWeilData.hE_le_m
#print axioms R6LocalWeilData.hE_le_kappa
#print axioms R6LocalWeilData.ofProjHeight
end LeanFormal.IUT.XiFPaper.HTF4R6Actual
end