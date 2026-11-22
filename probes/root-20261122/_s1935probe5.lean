import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

section SiteCompF

variable {A C : S1728Cover} (f : S1728CoverMap A C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteCompF_probe (x : ↥(A.source.fiber.obj U)) : S1890SiteCompF f φ ψ x := by
  unfold S1890SiteCompF
  rw [natCompHomApp]
  simp only [Category.assoc]
  rw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  simp

end SiteCompF

section SiteCompG

variable {B C : S1728Cover} (g : S1728CoverMap B C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteCompG_probe (y : ↥(B.source.fiber.obj U)) : S1890SiteCompG g φ ψ y := by
  unfold S1890SiteCompG
  rw [natCompInvApp]
  simp only [Category.assoc]
  rw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  simp

end SiteCompG

section SiteIdG

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem siteIdG_probe (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : S1890SiteIdG f g U := by
  intro x y h
  rw [Pseudofunctor.StrongTrans.naturality_id_inv]
  simp only [CategoryTheory.Cat.Hom₂.comp_app, CategoryTheory.Cat.whiskerRight_app,
    CategoryTheory.Cat.whiskerLeft_app, cat_leftUnitor_hom_app, cat_leftUnitor_inv_app,
    cat_rightUnitor_hom_app, cat_rightUnitor_inv_app]
  simp

end SiteIdG

end
