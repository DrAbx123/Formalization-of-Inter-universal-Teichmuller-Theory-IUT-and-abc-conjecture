import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainReachDirectedActual — upward directedness of Section-0 reachability

Genuine new theorem: every pair of vertices has a common reachable upper bound.
Self-contained proof via the Reach ↔ ≤ characterization.  No new paper input;
no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainReachDirectedActual

open LeanFormal.IUT.XiFPaper.Mzk1Section0GraphActual

theorem reach_trans_local {n m : ℤ} (hnm : Reach n m) :
    ∀ k : ℤ, Reach m k → Reach n k := by
  induction hnm with
  | refl n =>
      intro k hmk
      exact hmk
  | step hstep htail ih =>
      intro k hmk
      exact Reach.step hstep (ih k hmk)

theorem reach_nat_add_local (n : ℤ) (k : ℕ) : Reach n (n + (k : ℤ)) := by
  induction k with
  | zero =>
      simpa using Reach.refl n
  | succ k ih =>
      have hstep : SuccEdge (n + (k : ℤ)) (n + ((k + 1 : ℕ) : ℤ)) := by
        unfold SuccEdge
        push_cast
        ring
      exact reach_trans_local ih _ (Reach.step hstep (Reach.refl _))

theorem reach_of_le_local {n m : ℤ} (h : n ≤ m) : Reach n m := by
  have hnonneg : 0 ≤ m - n := sub_nonneg.mpr h
  have hm : m = n + ((m - n).toNat : ℤ) := by
    have hcast : (((m - n).toNat : ℤ)) = m - n := Int.toNat_of_nonneg hnonneg
    omega
  rw [hm]
  exact reach_nat_add_local n (m - n).toNat

theorem reach_common_upper (n m : ℤ) : ∃ k : ℤ, Reach n k ∧ Reach m k := by
  refine ⟨max n m, reach_of_le_local (le_max_left n m), reach_of_le_local (le_max_right n m)⟩

theorem reach_common_upper_le (n m : ℤ) : ∃ k : ℤ, n ≤ k ∧ m ≤ k ∧ Reach n k ∧ Reach m k := by
  refine ⟨max n m, le_max_left n m, le_max_right n m, ?_, ?_⟩
  · exact reach_of_le_local (le_max_left n m)
  · exact reach_of_le_local (le_max_right n m)

end LeanFormal.IUT.XiFPaper.Mzk1ChainReachDirectedActual

end
