/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Paper312UnramifiedActual
import tmp.sheaf.xif.paper.Mzk1Paper312FinalBoundActual
import Mathlib.Tactic
/-! # Assemble per-place correction bounds into A <= Lbar + Dbar -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Paper312AssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1Paper312FinalBoundActual
/-- `qlog/(2l)` equals the correction per-place coefficient. -/
theorem qlog_div_eq (fn Fdeg logp l : ℝ) :
    (fn / Fdeg * logp) / (2 * l) = fn / (Fdeg * (2 * l)) * logp := by
  field_simp
/-- Per-place correction bounds sum to `A <= Lbar + Dbar`. -/
theorem A_le_Lbar_add_Dbar_of_correction
    {ι : Type*} [Fintype ι] {l : ℝ}
    {fn Fdeg logp logIdx diff : ι → ℝ}
    (h : ∀ i, fn i / (Fdeg i * (2 * l)) * logp i ≤ logIdx i + diff i) :
    (1 / (2 * l)) * (∑ i, (fn i / Fdeg i * logp i)) ≤
      ∑ i, (logIdx i + diff i) := by
  apply A_le_Lbar_add_Dbar (qlog := fun i => fn i / Fdeg i * logp i)
  intro i
  rw [qlog_div_eq]
  exact h i
/-- Paper 3.12 from per-place correction bounds. -/
theorem paper312_of_correction_bounds
    {ι : Type*} [Fintype ι] {l sFactor : ℝ}
    {fn Fdeg logp logIdx diff : ι → ℝ}
    (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) * (∑ i, (fn i / Fdeg i * logp i)))
    (h : ∀ i, fn i / (Fdeg i * (2 * l)) * logp i ≤ logIdx i + diff i) :
    LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual.ExplicitPaper312Inequality
      sFactor ((1 / (2 * l)) * (∑ i, (fn i / Fdeg i * logp i)))
      (∑ i, logIdx i) (∑ i, diff i) := by
  have hsum := A_le_Lbar_add_Dbar_of_correction h
  have hsum' : (∑ i, (logIdx i + diff i)) =
      (∑ i, logIdx i) + ∑ i, diff i := Finset.sum_add_distrib
  rw [hsum'] at hsum
  exact LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual.explicitInequality_of_bounds
    hs0 hs1 hA0 hsum
end LeanFormal.IUT.XiFPaper.Mzk1Paper312AssemblyActual
end