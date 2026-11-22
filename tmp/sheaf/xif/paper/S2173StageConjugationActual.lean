import tmp.sheaf.xif.paper.S2169MuQZConjugationActual

-- S2173: actual Abelianization/torsion conjugation helpers; the open-subgroup
-- stage equivalence itself remains exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2173StageConjugationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Abelianization equivalence induced by a multiplicative equivalence. -/
noncomputable def abelianizationCongr {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) : Abelianization G ≃* Abelianization H where
  toFun := Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv x := by
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom =
        MonoidHom.id G := by ext y; simp
    have h : (Abelianization.map e.symm.toMonoidHom).comp
        (Abelianization.map e.toMonoidHom) = MonoidHom.id _ := by
      rw [Abelianization.map_comp, hcomp, Abelianization.map_id]
    exact DFunLike.congr_fun h x
  right_inv x := by
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom =
        MonoidHom.id H := by ext y; simp
    have h : (Abelianization.map e.toMonoidHom).comp
        (Abelianization.map e.symm.toMonoidHom) = MonoidHom.id _ := by
      rw [Abelianization.map_comp, hcomp, Abelianization.map_id]
    exact DFunLike.congr_fun h x
  map_mul' x y := map_mul _ x y

/-- Torsion equivalence induced by a multiplicative equivalence. -/
noncomputable def torsionCongr {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) : CommGroup.torsion G ≃* CommGroup.torsion H :=
  (MulEquiv.subgroupMap e (CommGroup.torsion G)).trans
    (MulEquiv.subgroupCongr (e.map_torsion))

/-- The subgroup-level conjugation equivalence H ≃* H.map (conj g). -/
noncomputable def S2173ConjSubgroupEquiv (g : Gv p) (H : Index p) :
    ↥H ≃* ↥(H.toSubgroup.map (MulAut.conj g).toMonoidHom) :=
  Subgroup.equivMapOfInjective H.toSubgroup
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective

/-- Exact missing: stage conjugation at the S2169 index. -/
abbrev S2173StageConjugationRequired (g : Gv p) : Type :=
  ∀ H : Index p, Stage p H ≃+ Stage p (S2169ConjIndex p g H)

#check abelianizationCongr
#check torsionCongr
#check S2173ConjSubgroupEquiv
#check S2173StageConjugationRequired

#print axioms abelianizationCongr
#print axioms torsionCongr
#print axioms S2173ConjSubgroupEquiv

end LeanFormal.IUT.XiFPaper.S2173StageConjugationActual

end