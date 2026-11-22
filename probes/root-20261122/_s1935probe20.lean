import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

universe u v

theorem natCompHomApp' {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (x : ↑(F.obj a)) :
    (α.naturality (f ≫ g)).hom.toNatTrans.app x =
      (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app x) ≫
            (G.mapComp f g).inv.toNatTrans.app ((α.app a).toFunctor.obj x) := by
  rw [Pseudofunctor.StrongTrans.naturality_comp_hom]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, CategoryTheory.Cat.associator_hom_app,
    CategoryTheory.Cat.associator_inv_app]
  simp

section SiteCompF

variable {A C : S1728Cover} (f : S1728CoverMap A C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteCompF_probe (x : ↥(A.source.fiber.obj U)) : S1890SiteCompF f φ ψ x := by
  unfold S1890SiteCompF
  rw [natCompHomApp']
  refine (Eq.trans ?_ ?_).symm
  · exact Category.assoc _ _ _
  · refine Eq.trans ?_ ?_
    · exact congrArg (fun t => _ ≫ t) (CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app _ _)
    · exact Category.comp_id _

end SiteCompF

end
