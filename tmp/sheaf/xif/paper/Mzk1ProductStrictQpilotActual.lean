/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1ProductStrictQpilotActual — product strictness (qpilot lane)

A578/A582: finite-product strictness for `ℝ≥0` factors: one strictly larger
factor plus positive factors gives a strictly larger product.  Proved by the
`Finset.mul_prod_erase` decomposition, avoiding strict-monotonicity typeclasses. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProductStrictQpilotActual

open scoped BigOperators
open scoped NNReal

/-- Finite-product strictness over `ℝ≥0`. -/
theorem nnreal_prod_strict {ι : Type} [Fintype ι] (f g : ι → ℝ≥0)
    (hpos : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i) (i0 : ι) (hlt : f i0 < g i0) :
    (∏ i, f i) < ∏ i, g i := by
  classical
  let A : ℝ≥0 := Finset.prod (Finset.univ.erase i0) f
  let B : ℝ≥0 := Finset.prod (Finset.univ.erase i0) g
  have hApos : 0 < A := Finset.prod_pos (fun i _ => hpos i)
  have hAeq : f i0 * A = ∏ i, f i :=
    Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i0)
  have hBeq : g i0 * B = ∏ i, g i :=
    Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i0)
  have hAB : A ≤ B := Finset.prod_le_prod' (fun i _ => hle i)
  have hleft : f i0 * A < g i0 * A := mul_lt_mul_of_pos_right hlt hApos
  have hright : g i0 * A ≤ g i0 * B := mul_le_mul_of_nonneg_left hAB (by positivity)
  rw [← hAeq, ← hBeq]
  exact lt_of_lt_of_le hleft hright

/-- Strictness in a single factor gives strictness of the full product. -/
theorem nnreal_prod_strict_single {ι : Type} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ≥0) (hpos : ∀ i, 0 < f i) (hle : ∀ i, f i ≤ g i)
    (hlt : ∃ i, f i < g i) : (∏ i, f i) < ∏ i, g i := by
  classical
  obtain ⟨i0, hi0⟩ := hlt
  exact nnreal_prod_strict f g hpos hle i0 hi0

/-- Product monotonicity (non-strict). -/
theorem nnreal_prod_mono {ι : Type} [Fintype ι] (f g : ι → ℝ≥0)
    (hle : ∀ i, f i ≤ g i) : (∏ i, f i) ≤ ∏ i, g i :=
  Finset.prod_le_prod' (fun i _ => hle i)

#check nnreal_prod_strict
#check nnreal_prod_strict_single

end LeanFormal.IUT.XiFPaper.Mzk1ProductStrictQpilotActual
end
