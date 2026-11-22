/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1NormArchCHArcActual
import Mathlib.Tactic

/-! # GAP-NORM-ARCH-C-K: explicit C_K = 1/[K:Q] arch normalization -/
noncomputable section
open scoped BigOperators NumberField
open LeanFormal.IUT.IUTIV.Estimates
namespace LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
open LeanFormal.IUT.XiFPaper.Mzk1NormArchCHArcActual
variable {K : Type*} [Field K] [NumberField K]
/-- Explicit arch normalization factor `C_K = 1/[K:Q]`. -/
noncomputable def archCK (K : Type*) [Field K] [NumberField K] : ℝ :=
  ((Module.finrank ℚ K : ℝ))⁻¹
/-- Explicit toric factor `1/(2[K:Q])`. -/
noncomputable def archCKToric (K : Type*) [Field K] [NumberField K] : ℝ :=
  ((2 : ℝ) * (Module.finrank ℚ K : ℝ))⁻¹
theorem archCK_pos : 0 < archCK K := by
  unfold archCK
  exact inv_pos.mpr (by exact_mod_cast Module.finrank_pos)
theorem archCKToric_pos : 0 < archCKToric K := by
  unfold archCKToric
  exact inv_pos.mpr (mul_pos (by norm_num) (by exact_mod_cast Module.finrank_pos))
theorem archCK_eq_heightWeight : archCK K = heightWeight K := rfl
theorem archCKToric_eq_toricHeightWeight :
    archCKToric K = toricHeightWeight K := rfl
/-- General-K arch term with explicit `C_K` factor. -/
theorem hArc_eq_archCK_mul_sum (x : K) :
    hArc K x = archCK K *
      ∑ w : NumberField.InfinitePlace K, hTerm K (.infinite w) x := by
  unfold hArc archCK
  rfl
/-- General-K finite part with explicit `C_K` factor. -/
theorem hNon_eq_archCK_mul_sum (x : K) :
    hNon K x = archCK K *
      ∑ v ∈ nonSupportFinset K x, hTerm K (.finite v) x := by
  unfold hNon archCK
  rfl
/-- General-K toric arch term with explicit `1/(2[K:Q])`. -/
theorem hToricArc_eq_archCKToric_mul_sum (x : K) :
    hToricArc K x = archCKToric K *
      ∑ w : NumberField.InfinitePlace K, toricTerm K (.infinite w) x := by
  unfold hToricArc archCKToric
  rfl
def normArchCKRows : List (String × String) :=
  [ ("archCK", "C_K = 1/[K:Q] explicit"),
    ("archCKToric", "1/(2[K:Q]) explicit"),
    ("hArc_eq_archCK_mul_sum", "general K arch factor"),
    ("hNon_eq_archCK_mul_sum", "general K finite factor"),
    ("hToricArc_eq_archCKToric_mul_sum", "general K toric factor"),
    ("NORM-ARCH-C-K", "CONDITIONAL/green explicit factor; abc output hookup GAP") ]
theorem normArchCKRows_length : normArchCKRows.length = 6 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1NormArchCKActual
