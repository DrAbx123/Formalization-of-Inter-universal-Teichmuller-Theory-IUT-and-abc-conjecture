import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainReachTransActual — transitivity of Section-0 reachability

Genuine new theorem: the successor-graph reachability relation Reach is
transitive.  Reuses the EXIT0 Section-0 graph definition and monotonicity.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainReachTransActual

open LeanFormal.IUT.XiFPaper.Mzk1Section0GraphActual

theorem reach_trans {n m : ℤ} (hnm : Reach n m) :
    ∀ k : ℤ, Reach m k → Reach n k := by
  induction hnm with
  | refl n =>
      intro k hmk
      exact hmk
  | step hstep htail ih =>
      intro k hmk
      exact Reach.step hstep (ih k hmk)

theorem reach_trans' {n m k : ℤ} (hnm : Reach n m) (hmk : Reach m k) :
    Reach n k :=
  reach_trans hnm k hmk

theorem reach_le_trans {n m k : ℤ} (hnm : Reach n m) (hmk : Reach m k) :
    n ≤ k := by
  exact reach_le (reach_trans' hnm hmk)

end LeanFormal.IUT.XiFPaper.Mzk1ChainReachTransActual

end
