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

section Proj

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

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

end Proj

section Extract

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
  {S : Site} {R : Sieve S}

noncomputable def S2004FstDescentData
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    A.source.fiber.DescentData (fun (i : R.arrows.category) => i.obj.hom) where
  obj i := (D.obj i).obj.left
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
      (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y gg q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    have hD := D.pullHom_hom gg q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    have h2 := congrArg (fun m =>
      (S1836IsoCommaFst (f.map.app (U Y')).toFunctor (g.map.app (U Y')).toFunctor).map m) hD
    rw [S2004Fst_pullHom_raw _ gg gf₁ gf₂ hgf₁ hgf₂] at h2
    exact h2
  hom_self Y q i mm hmm := by
    have hD := D.hom_self q mm hmm
    rw [hD]
    rfl
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have hD := D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃
    rw [← Functor.map_comp, hD]

end Extract

end LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual