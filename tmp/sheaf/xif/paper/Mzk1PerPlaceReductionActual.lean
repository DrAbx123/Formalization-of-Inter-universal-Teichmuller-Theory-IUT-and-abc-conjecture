/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A1078: per-place / parity reduction to the variant (pure algebra) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (REDUCTION ONLY, not a proof: the per-place/parity inequalities are hypotheses) |
| 真证 | `total_of_perPlace`; `total_of_parity` (disjoint/cover); `variant_of_perPlace`; `variant_of_parity` |
| GAP | GAP-LARGE-M: per-place/parity conditions are bounded-m statements; large-m needs Step (xi-d) or an explicit qOrder bound |
| GAP | GAP-PER-P: the per-p estimates (ind2 frac lower, V tame lower) are not proved here |
| 循环性 | no target assumed; the reduction is pure Finset algebra |
-/

noncomputable section
open Finset
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1PerPlaceReductionActual

variable {ι : Type*} [DecidableEq ι]

/-- Per-place deficit: every place satisfies `(sF-1)*A_p <= V_p + ind2_p`. -/
def PerPlaceDeficit (V ind2 A : ι → Real) (sF : Real) : Prop :=
  ∀ p, (sF - 1) * A p ≤ V p + ind2 p

/-- The total `M` in the per-place normalization. -/
def MOf [Fintype ι] (V ind2 A : ι → Real) (sF : Real) : Real :=
  (∑ p, (V p + ind2 p)) - (sF - 1) * (∑ p, A p)

/-- **Real reduction**: per-place deficit implies `0 <= M`. -/
theorem total_of_perPlace [Fintype ι] {V ind2 A : ι → Real} {sF : Real}
    (h : PerPlaceDeficit V ind2 A sF) : 0 ≤ MOf V ind2 A sF := by
  unfold MOf
  have hsum : (∑ p, (sF - 1) * A p) ≤ ∑ p, (V p + ind2 p) :=
    Finset.sum_le_sum fun p _ => h p
  rw [← Finset.mul_sum] at hsum
  linarith

/-- Parity deficit: odd and even groups each satisfy the deficit inequality. -/
def ParityDeficit [Fintype ι] (odd even : Finset ι) (V ind2 A : ι → Real)
    (sF : Real) : Prop :=
  ((sF - 1) * (∑ p ∈ odd, A p) ≤ ∑ p ∈ odd, (V p + ind2 p)) ∧
  ((sF - 1) * (∑ p ∈ even, A p) ≤ ∑ p ∈ even, (V p + ind2 p))

/-- **Real reduction (parity)**: disjoint/cover parity conditions imply `0 <= M`. -/
theorem total_of_parity [Fintype ι] {odd even : Finset ι}
    (hpart : Disjoint odd even) (hcover : odd ∪ even = Finset.univ)
    {V ind2 A : ι → Real} {sF : Real}
    (h : ParityDeficit odd even V ind2 A sF) : 0 ≤ MOf V ind2 A sF := by
  unfold MOf
  have hsum : (∑ p, (V p + ind2 p)) =
      (∑ p ∈ odd, (V p + ind2 p)) + (∑ p ∈ even, (V p + ind2 p)) := by
    rw [← Finset.sum_union hpart, hcover]
  have hA : (∑ p, A p) = (∑ p ∈ odd, A p) + (∑ p ∈ even, A p) := by
    rw [← Finset.sum_union hpart, hcover]
  rw [hsum, hA]
  nlinarith [h.1, h.2]

/-- Variant form of the per-place reduction. -/
theorem variant_of_perPlace [Fintype ι] {V ind2 A : ι → Real} {sF : Real}
    (h : PerPlaceDeficit V ind2 A sF) : 0 ≤ MOf V ind2 A sF :=
  total_of_perPlace h

/-- Variant form of the parity reduction. -/
theorem variant_of_parity [Fintype ι] {odd even : Finset ι}
    (hpart : Disjoint odd even) (hcover : odd ∪ even = Finset.univ)
    {V ind2 A : ι → Real} {sF : Real}
    (h : ParityDeficit odd even V ind2 A sF) : 0 ≤ MOf V ind2 A sF :=
  total_of_parity hpart hcover h

def perPlaceRows : List (String × String) :=
  [ ("PerPlaceDeficit / MOf", "definitions (per-place normalization)") ,
    ("total_of_perPlace", "PerPlaceDeficit -> 0 <= M (PROVED)") ,
    ("ParityDeficit", "odd/even group deficits") ,
    ("total_of_parity", "disjoint/cover parity -> 0 <= M (PROVED)") ,
    ("variant_of_perPlace / variant_of_parity", "variant-form wrappers (PROVED)") ,
    ("GAP-LARGE-M", "per-place/parity are bounded-m; large-m needs Step (xi-d)/qOrder bound") ]

theorem perPlaceRows_length : perPlaceRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1PerPlaceReductionActual