/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A772: arithmetic of the faithful theta scaling `scaleEltAt = qroot^{(i+1)^2}` -/

/- lana exact form (Iut/Concrete/ThetaRegion.lean):
* `distinguished i = ⟨i+1, _⟩` (:116-119), labels `j = i+1 ∈ {1,...,n}`;
* `scaleEltAt i p c l = incl( qroot(sectPlace (c l)) ^ ((i+1)^2) )` (:124-132),
  i.e. the scaling element is `qroot^{(i+1)^2}` in the l-th tensor factor;
* `qroot` (Data.lean:281 `qrootOf`, spec :287 `qroot^{2l} = q_v` at bad places, `1` elsewhere);
* `thetaFiniteOn = ⋃ φ ∈ indAut, φ '' (⋃ l ∈ S, scaleEltAt l • shell)` (:170-175): the theta
  component is the union over Ind1/2/3 automorphisms of the scaled log-shell.

Hence the faithful theta-pilot region at a finite place, for the distinguished label
`j = i+1`, is `qroot^{j^2} • logShell` up to the (log-volume preserving) indeterminacy
automorphisms.  Additive Haar scaling by `a` multiplies mass by `‖a‖`; with
`‖qroot‖^{2l} = ‖q‖` this gives the shift `j^2 * log‖qroot‖ = (j^2/(2l))*log‖q‖`.
Summing over the nC capsules divides by nC, giving coefficient `sFactor(nC)/(2l)`;
subtracting the q-side `1/(2l)` leaves `(sFactor(nC)-1)/(2l)`, i.e. lana's c_lana. -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaScaleArithmeticActual

/-- lana `sFactor n = (sum_{j<n} (j+1)^2)/n`. -/
def sFactor (n : ℕ) : ℝ := (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2) / (n : ℝ)

/-- Scaling shift of the distinguished label `j = i+1`: `j^2 * log‖qroot‖`. -/
def shiftedLog (j : ℕ) (logQroot : ℝ) : ℝ := (j : ℝ) ^ 2 * logQroot

/-- If `(2l) * log‖qroot‖ = log‖q‖` then the shift is `(j^2/(2l))*log‖q‖`. -/
theorem shiftedLog_eq (j : ℕ) (l logq logQroot : ℝ) (hl : l ≠ 0)
    (h : 2 * l * logQroot = logq) :
    shiftedLog j logQroot = ((j : ℝ) ^ 2 / (2 * l)) * logq := by
  unfold shiftedLog
  have h2 : logQroot = logq / (2 * l) := by
    field_simp [hl]
    linarith
  rw [h2]
  ring

/-- **Coefficient of the capsule average**: for n > 0,
`(1/n) * sum_{j<n} ((j+1)^2/(2l)) = sFactor n / (2l)`. -/
theorem capsule_average_coeff (n : ℕ) (hn : 0 < n) (l : ℝ) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 / (2 * l))) =
      sFactor n / (2 * l) := by
  have hsum : (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 / (2 * l)))
      = (∑ j ∈ Finset.range n, ((j : ℝ) + 1) ^ 2) / (2 * l) := by
    rw [← Finset.sum_div]
  rw [hsum]
  unfold sFactor
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp [hnR]

/-- **The c_lana coefficient**: capsule average minus the q-side `1/(2l)` is
`(sFactor n - 1)/(2l)`. -/
theorem clana_coeff (n : ℕ) (l : ℝ) :
    sFactor n / (2 * l) - 1 / (2 * l) = (sFactor n - 1) / (2 * l) := by
  field_simp

end LeanFormal.IUT.XiFPaper.Mzk1ThetaScaleArithmeticActual
