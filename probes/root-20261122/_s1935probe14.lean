import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
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

attribute [local reducible] CategoryTheory.Cat

universe u v

example {B C D : Cat.{0, 0}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := by
  rw [CategoryTheory.Cat.Hom.comp_obj]

section SiteCompF

variable {A C : S1728Cover} (f : S1728CoverMap A C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

-- directly test the naturality rewrite plus cancellation using explicit trans
theorem siteCompF_probe (x : ↥(A.source.fiber.obj U)) : S1890SiteCompF f φ ψ x := by
  unfold S1890SiteCompF
  rw [natCompHomApp]
  rw [Category.assoc]
  rw [CategoryTheory.Cat.Hom.inv_hom_id_toNatTrans_app]
  exact (Category.comp_id _).symm

end SiteCompF

end
