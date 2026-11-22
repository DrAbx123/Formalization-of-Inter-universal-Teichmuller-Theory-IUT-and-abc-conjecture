import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainReachMonoActual — monotonicity of Section-0 reachability

Genuine new theorem: Reach is monotone under widening both endpoints:
Reach n m, n' ≤ n, m ≤ m' imply Reach n' m'.  Self-contained proof via the
Reach ↔ ≤ characterization.  No new paper input; no closure; gate NOT PASSED. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainReachMonoActual

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

theorem reach_iff_le_local {n m : ℤ} : Reach n m ↔ n ≤ m := by
  constructor
  · intro h
    exact reach_le h
  · intro h
    have hnonneg : 0 ≤ m - n := sub_nonneg.mpr h
    have hm : m = n + ((m - n).toNat : ℤ) := by
      have hcast : (((m - n).toNat : ℤ)) = m - n := Int.toNat_of_nonneg hnonneg
      omega
    rw [hm]
    exact reach_nat_add_local n (m - n).toNat

theorem reach_mono {n m n' m' : ℤ} (h : Reach n m) (hn : n' ≤ n) (hm : m ≤ m') :
    Reach n' m' := by
  apply reach_iff_le_local.mpr
  exact le_trans hn (le_trans (reach_iff_le_local.mp h) hm)

theorem reach_mono_interval {n m : ℤ} (h : Reach n m) {n' m' : ℤ}
    (hn : n' ≤ n) (hm : m ≤ m') : Reach n' m' := reach_mono h hn hm

end LeanFormal.IUT.XiFPaper.Mzk1ChainReachMonoActual

end
