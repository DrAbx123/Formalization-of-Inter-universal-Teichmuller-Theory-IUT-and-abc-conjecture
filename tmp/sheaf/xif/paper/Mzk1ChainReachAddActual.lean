import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainReachAddActual — successor/nat-addition reachability

Genuine new theorems: Reach is preserved by one successor step, and every
nonnegative integer increment is reachable (induction on Nat).  Reuses the
EXIT0 successor graph and the transitivity chain.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainReachAddActual

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

theorem reach_succ {n m : ℤ} (h : Reach n m) : Reach n (m + 1) := by
  have hstep : SuccEdge m (m + 1) := by
    unfold SuccEdge
    ring
  exact reach_trans_local h (m + 1) (Reach.step hstep (Reach.refl (m + 1)))

theorem reach_nat_add (n : ℤ) (k : ℕ) : Reach n (n + (k : ℤ)) := by
  induction k with
  | zero =>
      simpa using Reach.refl n
  | succ k ih =>
      have hstep : SuccEdge (n + (k : ℤ)) (n + ((k + 1 : ℕ) : ℤ)) := by
        unfold SuccEdge
        push_cast
        ring
      exact reach_trans_local ih _ (Reach.step hstep (Reach.refl _))

theorem reach_nat_add_le (n : ℤ) (k : ℕ) : n ≤ n + (k : ℤ) := by
  exact reach_le (reach_nat_add n k)

end LeanFormal.IUT.XiFPaper.Mzk1ChainReachAddActual

end
