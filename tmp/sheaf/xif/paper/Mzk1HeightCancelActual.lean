/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1HeightCancelActual — §9 cancellation identity and the h_V lemma shape (A777)

ROUTES §9: the paper 3.12 reduces to lemma h_V on the height h_V of a divisible
Θ-object E with three properties:
  (i)  h_V(E) = (1/12)·log q;
  (ii) h_V(E/M) = l·h_V(E);
  (iii) h_V(E/M) − h_V(E) ≤ (l/2)·(log d + log f)  (up to an absolute constant).

Over the whole set of places the Galois symmetry argument gives only `0 = 0`:
at a multiplicative place the local degree gain is `l − 1`, at an étale place the
loss is `(l − 1)/l`; with weights `1/(l+1)` and `l/(l+1)` these cancel exactly:

  `(1/(l+1))·(l − 1) − (l/(l+1))·((l − 1)/l) = 0`   (`cancellation_identity`).

This file formalizes the identity, its weighted-sum form, and the shape of the h_V
lemma; it isolates the genuinely remaining input `h_V` (iii) as a named statement.
No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HeightCancelActual

open scoped BigOperators

/-! ### 1. Local degrees and weights -/

/-- Weight of a multiplicative place: `1/(l+1)`. -/
def weightMul (l : ℝ) : ℝ := 1 / (l + 1)

/-- Weight of an étale place: `l/(l+1)`. -/
def weightEtale (l : ℝ) : ℝ := l / (l + 1)

/-- Local degree gain at a multiplicative place: `l − 1`. -/
def degreeMul (l : ℝ) : ℝ := l - 1

/-- Local degree loss at an étale place: `(l − 1)/l`. -/
def degreeEtale (l : ℝ) : ℝ := (l - 1) / l

/-- **The §9 cancellation identity**: `(1/(l+1))·(l−1) = (l/(l+1))·((l−1)/l)`. -/
theorem cancellation_identity (l : ℝ) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * degreeMul l - weightEtale l * degreeEtale l = 0 := by
  unfold weightMul weightEtale degreeMul degreeEtale
  field_simp
  ring

/-- The two weighted local degrees are equal. -/
theorem weighted_degrees_eq (l : ℝ) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * degreeMul l = weightEtale l * degreeEtale l :=
  sub_eq_zero.mp (cancellation_identity l hl hl1)

/-- Per-place form: for any local order `m`, the weighted contributions cancel. -/
theorem per_place_cancellation (l m : ℝ) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * (degreeMul l * m) - weightEtale l * (degreeEtale l * m) = 0 := by
  rw [← mul_assoc, ← mul_assoc, weighted_degrees_eq l hl hl1, sub_self]

/-- Weighted-sum form over an arbitrary finite set of places: the net degree gain is `0`. -/
theorem weighted_sum_cancellation {ι : Type*} (s : Finset ι) (l : ℝ) (m : ι → ℝ)
    (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    (s.sum (fun i => weightMul l * (degreeMul l * m i))) -
      (s.sum (fun i => weightEtale l * (degreeEtale l * m i))) = 0 := by
  have hpt : ∀ i ∈ s, weightMul l * (degreeMul l * m i) =
      weightEtale l * (degreeEtale l * m i) := by
    intro i _
    rw [← mul_assoc, ← mul_assoc, weighted_degrees_eq l hl hl1]
  rw [Finset.sum_congr rfl hpt, sub_self]

/-! ### 2. The shape of the h_V lemma -/

/-- Data for the h_V lemma: a height function on an abstract carrier with a base
point and a scaling map (the quotient `E ↦ E/M`). -/
structure HVData (V : Type*) where
  /-- the height function `h_V`. -/
  hV : V → ℝ
  /-- the base object `E`. -/
  base : V
  /-- the scaling map `E ↦ E/M`. -/
  scale : V → V

/-- The three properties (i)-(iii) of the h_V lemma (ROUTES §9). -/
def HVLemmaStatement {V : Type*} (D : HVData V) (l q logd logf : ℝ) : Prop :=
  (D.hV D.base = (1 / 12) * Real.log q) ∧
  (∀ x : V, D.hV (D.scale x) = l * D.hV x) ∧
  (∀ x : V, D.hV (D.scale x) - D.hV x ≤ ((l : ℝ) / 2) * (logd + logf))

/-- Property (ii) gives the exact height difference: `h_V(E/M) − h_V(E) = (l−1)·h_V(E)`. -/
theorem hV_difference_of_scale {V : Type*} (D : HVData V) (l : ℝ)
    (hscale : ∀ x : V, D.hV (D.scale x) = l * D.hV x) (x : V) :
    D.hV (D.scale x) - D.hV x = (l - 1) * D.hV x := by
  rw [hscale x]
  ring

/-- At the base point the difference is `(l−1)·(1/12)·log q` (properties (i)+(ii)). -/
theorem hV_difference_base {V : Type*} (D : HVData V) (l q : ℝ)
    (hbase : D.hV D.base = (1 / 12) * Real.log q)
    (hscale : ∀ x : V, D.hV (D.scale x) = l * D.hV x) :
    D.hV (D.scale D.base) - D.hV D.base = (l - 1) * ((1 / 12) * Real.log q) := by
  rw [hV_difference_of_scale D l hscale D.base, hbase]

/-- **The cancellation says the local-degree bookkeeping is `0 = 0`**: the net of the
multiplicative gain and the étale loss over all places is zero, so the height
difference cannot be computed from local degrees — properties (i)+(ii) leave exactly
the bound (iii) as the remaining input. -/
theorem cancellation_net_zero (l : ℝ) (hl : l ≠ 0) (hl1 : l + 1 ≠ 0) :
    weightMul l * degreeMul l - weightEtale l * degreeEtale l = 0 :=
  cancellation_identity l hl hl1

/-! ### 3. Status rows -/

def heightCancelRows : List (String × String) :=
  [ ("§9 cancellation identity (weights 1/(l+1), l/(l+1); degrees l−1, (l−1)/l)",
     "PROVED"),
    ("per-place weighted cancellation", "PROVED"),
    ("weighted-sum cancellation over all places", "PROVED"),
    ("h_V lemma shape (i)+(ii)+(iii)", "DEFINED (HVLemmaStatement)"),
    ("h_V difference from (i)+(ii): (l−1)·(1/12)log q", "PROVED"),
    ("h_V bound (iii)", "NAMED — the single remaining input") ]

theorem heightCancelRows_length : heightCancelRows.length = 6 := rfl

#check cancellation_identity
#check weighted_sum_cancellation
#check HVLemmaStatement
#check hV_difference_base
#check heightCancelRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HeightCancelActual
end
