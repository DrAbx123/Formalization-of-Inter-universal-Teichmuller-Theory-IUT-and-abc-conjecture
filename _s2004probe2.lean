import tmp.sheaf.xif.paper.S1998IsoCommaPrestackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev J : GrothendieckTopology Site := SchemeOverField.etaleTopology K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem S2004Fst_pullHom_raw {X₁ X₂ Y Y' : Site}
    {M₁ : (sitePseudofunctor f g).obj (U X₁)} {M₂ : (sitePseudofunctor f g).obj (U X₂)}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (u : ((sitePseudofunctor f g).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
         ((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.obj M₂)
    (gg : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : gg ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : gg ≫ f₂ = gf₂ := by cat_disch) :
    (S1836IsoCommaFst (f.map.app (U Y')).toFunctor (g.map.app (U Y')).toFunctor).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := sitePseudofunctor f g) u gg gf₁ gf₂
          hgf₁ hgf₂) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := A.source.fiber)
        ((S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map u)
        gg gf₁ gf₂ hgf₁ hgf₂ := by
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [S1956Fst_mapComp', S1956Fst_map, S1956Fst_mapComp'_inv]

end LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual
