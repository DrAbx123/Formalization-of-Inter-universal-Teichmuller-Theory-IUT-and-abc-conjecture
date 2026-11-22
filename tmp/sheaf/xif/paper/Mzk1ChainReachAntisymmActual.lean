import tmp.sheaf.xif.paper.Mzk1Section0GraphActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainReachAntisymmActual — antisymmetry of Section-0 reachability

Genuine new theorem: mutual reachability in the successor graph forces equality
(antisymmetry).  Reuses reachability monotonicity and constructs the iff form.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainReachAntisymmActual

open LeanFormal.IUT.XiFPaper.Mzk1Section0GraphActual

theorem reach_antisymm {n m : ℤ} (hnm : Reach n m) (hmn : Reach m n) : n = m := by
  exact le_antisymm (reach_le hnm) (reach_le hmn)

theorem reach_mutual_iff_eq {n m : ℤ} :
    (Reach n m ∧ Reach m n) ↔ n = m := by
  constructor
  · rintro ⟨hnm, hmn⟩
    exact reach_antisymm hnm hmn
  · intro h
    subst h
    exact ⟨Reach.refl n, Reach.refl n⟩

theorem reach_self (n : ℤ) : Reach n n := Reach.refl n

end LeanFormal.IUT.XiFPaper.Mzk1ChainReachAntisymmActual

end
