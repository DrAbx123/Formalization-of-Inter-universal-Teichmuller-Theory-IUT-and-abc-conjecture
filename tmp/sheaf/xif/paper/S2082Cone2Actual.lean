import tmp.sheaf.xif.paper.S2081Cone1Actual

/-! # S2082: cone2 commutativity for a general cone

Mirrors S1985 `cone2_commutes_app` with `S2078ConeAt/LiftApp`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2082Cone2Actual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual
open LeanFormal.IUT.XiFPaper.S2077ComponentIsoActual
open LeanFormal.IUT.XiFPaper.S2080ConeAtCommutesActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem S2082lift_fst_obj (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(c.W.obj U)) :
    ((S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
      (S2078ConeAt f g c U)).obj x).obj.left =
      (c.toA.app U).toFunctor.obj x := rfl

theorem S2082lift_snd_obj (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(c.W.obj U)) :
    ((S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
      (S2078ConeAt f g c U)).obj x).obj.right =
      (c.toB.app U).toFunctor.obj x := rfl

theorem S2082ConeAt_commutes_app' (c : S2074GeneralCone f g)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) (x : ↑(c.W.obj U)) :
    ((S2078ConeAt f g c U).commutes.app x).hom =
      (c.commutes.hom.as.app U).toNatTrans.app x := by
  dsimp only [S2078ConeAt, S2077ComponentIso, CategoryTheory.Cat.Hom.toNatIso]
  rw [NatIso.trans_app, NatIso.trans_app]
  rw [Iso.trans_hom, Iso.trans_hom]
  rw [S2080_eqToIso_app_hom, S2080_eqToIso_app_hom]
  simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem S2082cone2_commutes_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↑(c.W.obj U)).obj
          (S2078LiftApp f g c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)).commutes.hom.app x =
      (S1864SiteComparisonLeft f φ).hom.app ((c.toA.app U).toFunctor.obj x) ≫
        (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
          (S1864SiteComparisonRight g φ).hom.app ((c.toB.app U).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((S1864IsoCommaRestrict (A.source.fiber.map φ).toFunctor
      (B.source.fiber.map φ).toFunctor (C.source.fiber.map φ).toFunctor
      (S1864SiteComparisonLeft f φ) (S1864SiteComparisonRight g φ)).obj
        ((S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
          (S2078ConeAt f g c U)).obj x)).obj.hom = _
  rw [S1864IsoCommaRestrict_obj_hom]
  rw [S1893Lift_structure]
  rw [S2082ConeAt_commutes_app']
  rfl

#print axioms S2082cone2_commutes_app

end LeanFormal.IUT.XiFPaper.S2082Cone2Actual

end
