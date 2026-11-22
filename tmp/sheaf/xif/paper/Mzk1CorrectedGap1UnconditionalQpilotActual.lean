/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1CorrectedGap1UnconditionalQpilotActual — corrected Gap1 assembly (A675)

Self-contained (Mathlib-only) assembly of the corrected-region Gap-1: the
multiplicative comparison, the ratio form and the log form are equivalent for the
inverse-prime-power corrected region volume.  This rewrite removes the dependency
on the queued scaling-log-law chain (which re-derives the same interface-level
statements).  B1/B2/B3 division of labour is recorded. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalQpilotActual

universe u

open scoped BigOperators

/-- Inverse-prime-power ratio `∏ (f_i^{e_i})⁻¹`. -/
noncomputable def invRatio {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat) : Real :=
  ∏ i, (f i ^ e i)⁻¹

theorem invRatio_pos {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat)
    (hf : ∀ i, 0 < f i) : 0 < invRatio f e :=
  Finset.prod_pos (fun i _ => inv_pos.mpr (pow_pos (hf i) _))

theorem invRatio_log {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat)
    (hf : ∀ i, 0 < f i) :
    Real.log (invRatio f e) = -∑ i, (e i : Real) * Real.log (f i) := by
  unfold invRatio
  have hpos : ∀ i, (f i ^ e i)⁻¹ ≠ 0 := fun i =>
    ne_of_gt (inv_pos.mpr (pow_pos (hf i) _))
  rw [Real.log_prod (fun i _ => hpos i)]
  have hterm : ∀ i, Real.log ((f i ^ e i)⁻¹) = -((e i : Real) * Real.log (f i)) := by
    intro i
    rw [Real.log_inv, Real.log_pow]
  simp only [hterm]
  rw [Finset.sum_neg_distrib]

/-- Corrected region volume `∏ (f^e)⁻¹ · base`. -/
noncomputable def correctedVol {ι : Type u} [Fintype ι] (f : ι → Real)
    (e : ι → Nat) (base : Real) : Real :=
  invRatio f e * base

theorem correctedVol_pos {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat)
    (base : Real) (hf : ∀ i, 0 < f i) (hb : 0 < base) : 0 < correctedVol f e base := by
  unfold correctedVol
  exact mul_pos (invRatio_pos f e hf) hb

theorem correctedVol_log {ι : Type u} [Fintype ι] (f : ι → Real) (e : ι → Nat)
    (base : Real) (hf : ∀ i, 0 < f i) (hb : 0 < base) :
    Real.log (correctedVol f e base) =
      Real.log base - ∑ i, (e i : Real) * Real.log (f i) := by
  unfold correctedVol
  rw [Real.log_mul (ne_of_gt (invRatio_pos f e hf)) (ne_of_gt hb), invRatio_log f e hf]
  ring

/-- **Corrected Gap-1 unconditional assembly**: multiplicative ↔ log form. -/
theorem corrected_gap1_unconditional {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (heps : 0 < 1 + epsilon) :
    (h ≤ (1 + epsilon) * correctedVol f e base) ↔
      (Real.log h ≤ Real.log (1 + epsilon) +
        (Real.log base - ∑ i, (e i : Real) * Real.log (f i))) := by
  have hv : 0 < correctedVol f e base := correctedVol_pos f e base hf hb
  have hprod : 0 < (1 + epsilon) * correctedVol f e base := mul_pos heps hv
  have hval : Real.log ((1 + epsilon) * correctedVol f e base) =
      Real.log (1 + epsilon) +
        (Real.log base - ∑ i, (e i : Real) * Real.log (f i)) := by
    rw [Real.log_mul (ne_of_gt heps) (ne_of_gt hv), correctedVol_log f e base hf hb]
  constructor
  · intro h1
    have hlog := Real.log_le_log hh h1
    rw [hval] at hlog
    exact hlog
  · intro hlog
    have : Real.log h ≤ Real.log ((1 + epsilon) * correctedVol f e base) := by
      rw [hval]
      exact hlog
    exact (Real.log_le_log_iff hh hprod).mp this

theorem corrected_gap1_from_log {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (hh : 0 < h) (heps : 0 < 1 + epsilon)
    (hlog : Real.log h ≤ Real.log (1 + epsilon) +
        (Real.log base - ∑ i, (e i : Real) * Real.log (f i))) :
    h ≤ (1 + epsilon) * correctedVol f e base :=
  (corrected_gap1_unconditional f e base hf hb hh heps).mpr hlog

theorem corrected_gap1_ratio {ι : Type u} [Fintype ι] {h epsilon : Real}
    (f : ι → Real) (e : ι → Nat) (base : Real) (hf : ∀ i, 0 < f i)
    (hb : 0 < base) (h1 : h ≤ (1 + epsilon) * correctedVol f e base) :
    h / correctedVol f e base ≤ 1 + epsilon :=
  (div_le_iff₀ (correctedVol_pos f e base hf hb)).mpr h1

/-- B1/B2/B3 division of labour. -/
def bDivisionRows : List (String × String × String) :=
  [ ("B1: singleton null measure", "hull lane (green model)",
     "single-point zero measure"),
    ("B2: normalization split", "mainline lane",
     "normalized volume split"),
    ("B3: corrected Gap1 unconditional", "qpilot lane (this file, Mathlib-only)",
     "corrected_gap1_unconditional") ]

theorem bDivisionRows_length : bDivisionRows.length = 3 := rfl

#check corrected_gap1_unconditional
#check corrected_gap1_ratio
#check bDivisionRows_length

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalQpilotActual
end
