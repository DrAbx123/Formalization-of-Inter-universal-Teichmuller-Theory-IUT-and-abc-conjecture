/-
Probe S1935 #1: check definitional equalities and direct proof attempt for SiteCompF.
-/
import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
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

universe u

example {B C D : Cat.{u, u}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := rfl

example {B : Cat.{u, u}} (Y : ↑B) : (𝟙 B : B ⟶ B).toFunctor.obj Y = Y := rfl

example {B C D : Cat.{u, u}} (F : B ⟶ C) (G : C ⟶ D) (X : ↑B) :
    (F ≫ G).toFunctor.obj X = G.toFunctor.obj (F.toFunctor.obj X) := by
  rw [CategoryTheory.Cat.Hom.comp_obj]

example {B : Cat.{u, u}} (Y : ↑B) : (𝟙 B : B ⟶ B).toFunctor.obj Y = Y := by
  rw [CategoryTheory.Cat.Hom.id_obj]

end
