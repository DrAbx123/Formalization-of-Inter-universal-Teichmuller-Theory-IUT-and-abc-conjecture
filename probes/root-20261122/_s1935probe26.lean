import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
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

universe u v

example {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G) {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (x : ↑(F.obj a)) :
    (α.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app x)
      = ((F.mapComp f g).hom ▷ α.app c).toNatTrans.app x := by
  rw [CategoryTheory.Cat.whiskerRight_app]

example {B : Type u} [Bicategory B] {F G : B ⥤ᵖ Cat.{v, v}}
    (α : Pseudofunctor.StrongTrans F G) {a b : B} (x : ↑(F.obj a)) :
    (G.mapId a).hom.toNatTrans.app ((α.app a).toFunctor.obj x)
      = (α.app a ◁ (G.mapId a).hom).toNatTrans.app x := by
  rw [CategoryTheory.Cat.whiskerLeft_app]

end
