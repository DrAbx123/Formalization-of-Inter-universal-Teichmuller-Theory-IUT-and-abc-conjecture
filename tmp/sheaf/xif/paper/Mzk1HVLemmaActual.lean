/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import Mathlib.Tactic

/-! # Mzk1HVLemmaActual — §9 h_V lemma: cancellation, statement, reduction (A779)

ROUTES §9: paper 3.12 reduces to the h_V lemma for a height `h_V` on a divisible
Theta-object `E` (three properties), while the global Galois-weighted local-degree
bookkeeping cancels exactly: `(1/(l+1))·(l−1) = (l/(l+1))·((l−1)/l)`; the local
degrees give only `0 = 0`, so the whole content is the h_V lemma.

Contents:
1. cancellation identity (real arithmetic), per place and for finite sums;
2. `HVLemmaStatement` with (i),(ii),(iii) and `hVLemma → SSIneq` (scaled comparison);
3. property (iii) reduced to the per-place different/conductor sum plus the
   dictionary `Σ d_p log p = log d`, `Σ δ_p log p = log f`;
4. status rows: what is proved, what property (iii) still needs.

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HVLemmaActual

open scoped BigOperators

/-! ### 1. Weights, local degrees, cancellation -/

def weightMul (l : Real) : Real := 1 / (l + 1)
def weightEtale (l : Real) : Real := l / (l + 1)
def degreeMul (l : Real) : Real := l - 1
def degreeEtale (l : Real) : Real := (l - 1) / l

/-- Cancellation identity. -/
theorem cancellation_identity (l : Real) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * degreeMul l - weightEtale l * degreeEtale l = 0 := by
  unfold weightMul weightEtale degreeMul degreeEtale
  field_simp
  ring

theorem weighted_degrees_eq (l : Real) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * degreeMul l = weightEtale l * degreeEtale l :=
  sub_eq_zero.mp (cancellation_identity l hl hl1)

theorem per_place_cancellation (l m : Real) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * (degreeMul l * m) - weightEtale l * (degreeEtale l * m) = 0 := by
  rw [← mul_assoc, ← mul_assoc, weighted_degrees_eq l hl hl1, sub_self]

/-- Weighted-sum form over any finite set of places. -/
theorem weighted_sum_cancellation {iota : Type*} (s : Finset iota) (l : Real) (m : iota → Real)
    (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    (s.sum (fun i => weightMul l * (degreeMul l * m i))) -
      (s.sum (fun i => weightEtale l * (degreeEtale l * m i))) = 0 := by
  have hpt : ∀ i ∈ s, weightMul l * (degreeMul l * m i) =
      weightEtale l * (degreeEtale l * m i) := by
    intro i _
    rw [← mul_assoc, ← mul_assoc, weighted_degrees_eq l hl hl1]
  rw [Finset.sum_congr rfl hpt, sub_self]

/-! ### 2. The h_V lemma statement -/

structure HVData (V : Type*) where
  hV : V → Real
  base : V
  scale : V → V

/-- The h_V lemma (i)+(ii)+(iii). -/
def HVLemmaStatement {V : Type*} (D : HVData V) (l q logd logf : Real) : Prop :=
  (D.hV D.base = (1 / 12) * Real.log q) ∧
  (∀ x : V, D.hV (D.scale x) = l * D.hV x) ∧
  (∀ x : V, D.hV (D.scale x) - D.hV x ≤ (l / 2) * (logd + logf))

/-- SSIneq explicit form. -/
def ssIneqBound (l logq V : Real) : Prop := ((l + 1) / 24 - 1 / (2 * l)) * logq ≤ V

/-- h_V lemma ⇒ SSIneq (scaled comparison). -/
theorem hVLemma_implies_ssIneq {V : Type*} (D : HVData V) {l q logd logf : Real}
    (hl : 0 < l) (hq : 0 ≤ Real.log q)
    (hbase : D.hV D.base = (1 / 12) * Real.log q)
    (hscale : ∀ x : V, D.hV (D.scale x) = l * D.hV x) :
    ssIneqBound l (Real.log q) (D.hV (D.scale D.base)) := by
  unfold ssIneqBound
  rw [hscale D.base, hbase]
  have hcoef : (l + 1) / 24 - 1 / (2 * l) ≤ l / 12 := by
    have hpos : (0 : Real) < l := hl
    have hdiff : l / 12 - ((l + 1) / 24 - 1 / (2 * l)) =
        (l - 1) / 24 + 1 / (2 * l) := by
      field_simp
      ring
    have hnonneg : 0 ≤ l / 12 - ((l + 1) / 24 - 1 / (2 * l)) := by
      rw [hdiff]
      have hfrac : (l - 1) / 24 + 1 / (2 * l) = (l ^ 2 - l + 12) / (24 * l) := by
        field_simp
        ring
      rw [hfrac]
      have hnum : (0 : ℝ) < l ^ 2 - l + 12 := by
        nlinarith [sq_nonneg (l - 1 / 2)]
      have hden : (0 : ℝ) < 24 * l := by positivity
      exact div_nonneg (le_of_lt hnum) (le_of_lt hden)
    linarith
  have hmul : ((l + 1) / 24 - 1 / (2 * l)) * Real.log q ≤
      (l / 12) * Real.log q :=
    mul_le_mul_of_nonneg_right hcoef hq
  have heq : (l / 12) * Real.log q = l * (1 / 12 * Real.log q) := by ring
  calc ((l + 1) / 24 - 1 / (2 * l)) * Real.log q
      ≤ (l / 12) * Real.log q := hmul
    _ = l * (1 / 12 * Real.log q) := heq

/-! ### 3. Property (iii) reduced to the different/conductor input -/

theorem hV_iii_of_perplace {l hVdiff diffSum condSum logd logf : Real}
    (hH : hVdiff ≤ (l / 2) * (diffSum + condSum))
    (hdict : diffSum = logd) (fdict : condSum = logf) :
    hVdiff ≤ (l / 2) * (logd + logf) := by
  rw [hdict, fdict] at hH
  exact hH

theorem hV_iii_iff_perplace {l hVdiff diffSum condSum logd logf : Real}
    (hdict : diffSum = logd) (fdict : condSum = logf) :
    (hVdiff ≤ (l / 2) * (diffSum + condSum)) ↔
      (hVdiff ≤ (l / 2) * (logd + logf)) := by
  rw [hdict, fdict]

/-! ### 4. Status rows -/

def hvLemmaRows : List (String × String) :=
  [ ("§9 cancellation identity", "PROVED (real arithmetic)"),
    ("per-place and weighted-sum cancellation", "PROVED"),
    ("h_V lemma statement (i)+(ii)+(iii)", "DEFINED (HVLemmaStatement)"),
    ("h_V (i)+(ii) => SSIneqExplicit", "PROVED (hVLemma_implies_ssIneq)"),
    ("property (iii) from per-place different/conductor sum", "PROVED (conditional)"),
    ("green per-place different bounds (LocalDifferentUpperBound/Order)",
     "AVAILABLE (per-place order bounds only)"),
    ("scaled theta volume difference = different/conductor sum", "MISSING"),
    ("dictionary Sum d_p log p = log d, Sum delta_p log p = log f", "MISSING"),
    ("archimedean contribution", "MISSING") ]

theorem hvLemmaRows_length : hvLemmaRows.length = 9 := rfl

#check cancellation_identity
#check hVLemma_implies_ssIneq
#check hV_iii_of_perplace
#check hvLemmaRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HVLemmaActual
end
