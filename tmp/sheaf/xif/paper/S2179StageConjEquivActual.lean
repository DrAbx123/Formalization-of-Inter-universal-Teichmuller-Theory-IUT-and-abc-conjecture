import tmp.sheaf.xif.paper.S2173StageConjugationActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The subgroup identification H.map(conj g.symm) = H.comap(conj g). -/
theorem S2179MapConjEqComap (g : Gv p) (H : Index p) :
    H.toSubgroup.map (MulAut.conj g.symm).toMonoidHom =
      H.toSubgroup.comap (MulAut.conj g).toMonoidHom := by
  change H.toSubgroup.map (MulAut.conj g.symm) =
    H.toSubgroup.comap (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_equiv_eq_comap_symm]
  rfl

/-- Actual stage conjugation equivalence. -/
noncomputable def S2179StageConj (g : Gv p) (H : Index p) :
    Stage p H ≃+ Stage p (S2169ConjIndex p g H) := by
  let e : ↥H ≃* ↥(H.toSubgroup.map (MulAut.conj g.symm).toMonoidHom) :=
    Subgroup.equivMapOfInjective H.toSubgroup
      (MulAut.conj g.symm).toMonoidHom (MulAut.conj g.symm).injective
  have h := S2179MapConjEqComap p g H
  let e' : ↥H ≃* ↥(H.toSubgroup.comap (MulAut.conj g).toMonoidHom) := h ▸ e
  exact (torsionCongr (abelianizationCongr e')).toAdditive

/-- The S2169 required type is inhabited. -/
noncomputable def S2179StageConjugationRequired_actual (g : Gv p) :
    S2169StageConjugationRequired p g :=
  fun H => S2179StageConj p g H

/-- Exact transfer compatibility surface. -/
def S2179TransferCompatible : Prop :=
  ∀ (g : Gv p) (H K : Index p) (h : H ≤ K) (v : Stage p K),
    ∃ h' : S2169ConjIndex p g H ≤ S2169ConjIndex p g K,
      S2179StageConj p g H (toStage p h v) =
        toStage p h' (S2179StageConj p g K v)

#check S2179MapConjEqComap
#check S2179StageConj
#check S2179StageConjugationRequired_actual
#check S2179TransferCompatible

#print axioms S2179MapConjEqComap
#print axioms S2179StageConj
#print axioms S2179StageConjugationRequired_actual

end LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

end