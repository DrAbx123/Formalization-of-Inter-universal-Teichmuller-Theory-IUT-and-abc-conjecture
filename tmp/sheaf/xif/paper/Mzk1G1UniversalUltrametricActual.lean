/- Route 7.2 Eisenstein valuation, auxiliary ultrametric lemma: in an ultrametric normed field
a finite sum with a unique strictly largest term has norm equal to that term. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUltrametricActual

open scoped BigOperators

variable {R : Type*} [NormedField R] [IsUltrametricDist R]

/-- Finite sums with a unique strictly largest term: the norm of the sum is the norm of the
largest term. -/
theorem norm_sum_eq_of_unique_max {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → R}
    {i0 : ι} (h : ∀ i, i ≠ i0 → ‖f i‖ < ‖f i0‖) : ‖∑ i, f i‖ = ‖f i0‖ := by
  classical
  have hs : (Finset.univ : Finset ι).Nonempty := ⟨i0, Finset.mem_univ i0⟩
  have hle : ‖∑ i : ι, f i‖ ≤ ‖f i0‖ := by
    refine (hs.norm_sum_le_sup'_norm f).trans ?_
    refine Finset.sup'_le hs _ ?_
    intro i _
    by_cases hii : i = i0
    · subst hii
      exact le_rfl
    · exact (h i hii).le
  by_cases h0 : ‖f i0‖ = 0
  · have hsingle : (∑ i : ι, f i) = f i0 := by
      refine Finset.sum_eq_single i0 ?_ ?_
      · intro b _ hb
        exfalso
        have := h b hb
        rw [h0] at this
        exact not_lt.mpr (norm_nonneg (f b)) this
      · intro hnotmem
        exact absurd (Finset.mem_univ i0) hnotmem
    rw [hsingle, h0]
  · have hpos : 0 < ‖f i0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have hother_lt : ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ < ‖f i0‖ := by
      rcases (Finset.univ.erase i0).eq_empty_or_nonempty with he | hne
      · simp [he, hpos]
      · refine (hne.norm_sum_le_sup'_norm f).trans_lt ?_
        rw [Finset.sup'_lt_iff]
        intro i hi
        exact h i (Finset.ne_of_mem_erase hi)
    have hdecomp : f i0 = (∑ i : ι, f i) + (-(∑ i ∈ (Finset.univ.erase i0), f i)) := by
      have hsum := Finset.sum_erase_add (Finset.univ : Finset ι) f (Finset.mem_univ i0)
      change f i0 = (∑ i ∈ (Finset.univ : Finset ι), f i) + (-(∑ i ∈ (Finset.univ.erase i0), f i))
      rw [← hsum]
      abel
    have hupper : ‖f i0‖ ≤ max ‖∑ i : ι, f i‖ ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ := by
      calc ‖f i0‖ = ‖(∑ i : ι, f i) + (-(∑ i ∈ (Finset.univ.erase i0), f i))‖ := by rw [hdecomp]
        _ ≤ max ‖∑ i : ι, f i‖ ‖-(∑ i ∈ (Finset.univ.erase i0), f i)‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ = max ‖∑ i : ι, f i‖ ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ := by rw [norm_neg]
    refine le_antisymm hle ?_
    by_contra hnot
    push_neg at hnot
    rcases le_total ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ ‖∑ i : ι, f i‖ with hOS | hSO
    · have hmax : max ‖∑ i : ι, f i‖ ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ =
          ‖∑ i : ι, f i‖ := max_eq_left hOS
      linarith
    · have hmax : max ‖∑ i : ι, f i‖ ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ =
          ‖(∑ i ∈ (Finset.univ.erase i0), f i)‖ := max_eq_right hSO
      linarith

#print axioms norm_sum_eq_of_unique_max
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUltrametricActual
