/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCAbcActual
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import Mathlib.Tactic

/-! # GAP-NORM-ARCH-C: degree-one/ℚ instantiation of IUT IV hArc / hToricArc -/

/-
| field | value |
|---|---|
| Status | green attempt: for `F=ℚ` (and degree-one K) the IUT IV arch terms are exactly the unweighted sums: `hArc = ∑ hTerm`, `hToricArc = (1/2)·∑ toricTerm`, `hNon = ∑ hTerm` |
| Reuse | `ArithmeticDivisorDegree.lean:1220/1224/1235`（hNon/hArc/hToricArc 定义）; `Mzk1NormArchCAbcActual.heightWeight_rat/toricHeightWeight_rat`（green） |
| GAP | general number field F ≠ ℚ needs `[F:Q]`/degree-one instance; only conditional forms are provided |
| 纪律 | no sorry/axiom; no new assumptions |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchCHArcActual

open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCAbcActual

/-- Over ℚ the IUT IV arch term is the unweighted infinite-place sum. -/
theorem hArc_rat (x : ℚ) :
    hArc ℚ x =
      ∑ w : NumberField.InfinitePlace ℚ, hTerm ℚ (.infinite w) x := by
  unfold hArc
  rw [heightWeight_rat, one_mul]

/-- Over ℚ the toric arch term carries the toric factor `1/2`. -/
theorem hToricArc_rat (x : ℚ) :
    hToricArc ℚ x =
      (1 / 2) * ∑ w : NumberField.InfinitePlace ℚ, toricTerm ℚ (.infinite w) x := by
  unfold hToricArc
  rw [toricHeightWeight_rat]

/-- Over ℚ the finite-part hNon is also unweighted. -/
theorem hNon_rat (x : ℚ) :
    hNon ℚ x =
      ∑ v ∈ nonSupportFinset ℚ x, hTerm ℚ (.finite v) x := by
  unfold hNon
  rw [heightWeight_rat, one_mul]

/-- Conditional degree-one form of the arch term. -/
theorem hArc_eq_sum_of_finrank_one
    {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) (x : K) :
    hArc K x =
      ∑ w : NumberField.InfinitePlace K, hTerm K (.infinite w) x := by
  unfold hArc
  rw [heightWeight_eq_one_of_finrank_one h, one_mul]

/-- Conditional degree-one form of the toric arch term. -/
theorem hToricArc_eq_half_mul_sum_of_finrank_one
    {K : Type*} [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) (x : K) :
    hToricArc K x =
      (1 / 2) * ∑ w : NumberField.InfinitePlace K, toricTerm K (.infinite w) x := by
  unfold hToricArc
  rw [toricHeightWeight_eq_half_of_finrank_one h]

def normArchCHArcRows : List (String × String) :=
  [ ("hArc_rat", "hArc ℚ = ∑ hTerm over infinite places") ,
    ("hToricArc_rat", "hToricArc ℚ = (1/2) * ∑ toricTerm") ,
    ("hNon_rat", "hNon ℚ = ∑ hTerm over finite support") ,
    ("hArc_eq_sum_of_finrank_one", "degree-one K arch = unweighted sum") ,
    ("hToricArc_eq_half_mul_sum_of_finrank_one", "degree-one K toric = 1/2 unweighted sum") ,
    ("GAP-NORM-ARCH-K", "general F without degree-one instance keeps 1/[F:Q] weight") ]

theorem normArchCHArcRows_length : normArchCHArcRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NormArchCHArcActual