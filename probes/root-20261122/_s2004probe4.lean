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
set_option pp.all false
set_option pp.proofs false

namespace LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1988HComparisonNaturalityActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

theorem S2004Push_coherence
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    {X₁ X₂ Y Y' : Site} {M : F.obj (U X₁)} {N : F.obj (U X₂)}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} (gg : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (h₁ : gg ≫ f₁ = gf₁) (h₂ : gg ≫ f₂ = gf₂)
    (u : (F.map f₁.op.toLoc).toFunctor.obj M ⟶ (F.map f₂.op.toLoc).toFunctor.obj N) :
    (α.naturality gf₁.op.toLoc).inv.toNatTrans.app M ≫
        (α.app (U Y')).toFunctor.map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F) u gg gf₁ gf₂ h₁ h₂) ≫
          (α.naturality gf₂.op.toLoc).hom.toNatTrans.app N =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := G)
        ((α.naturality f₁.op.toLoc).inv.toNatTrans.app M ≫
          (α.app (U Y)).toFunctor.map u ≫
            (α.naturality f₂.op.toLoc).hom.toNatTrans.app N) gg gf₁ gf₂ h₁ h₂ := by
  have hφ₁ : f₁.op.toLoc ≫ gg.op.toLoc = gf₁.op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← CategoryTheory.op_comp, h₁]
  have hφ₂ : f₂.op.toLoc ≫ gg.op.toLoc = gf₂.op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← CategoryTheory.op_comp, h₂]
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp, Category.assoc]
  -- abbreviations
  have key₁ := natCompInvApp_comp_mapComp' (F := F) (G := G) (α := α)
    (f := f₁.op.toLoc) (g := gg.op.toLoc) (fg := gf₁.op.toLoc) hφ₁ (x := M)
  have key₂ := natCompHomApp_comp_mapComp' (F := F) (G := G) (α := α)
    (f := f₂.op.toLoc) (g := gg.op.toLoc) (fg := gf₂.op.toLoc) hφ₂ (x := N)
  have keyQ := (α.naturality gg.op.toLoc).inv.toNatTrans.naturality u
  simp only [Cat.Hom.comp_map, Functor.comp_map] at keyQ
  have hA₂ : (F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N ≫
      (F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app N = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, (F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv_hom_id,
      Cat.Hom₂.id_app]
  have hmapA₂ : (α.app (U Y')).toFunctor.map
      ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N) ≫
      (α.app (U Y')).toFunctor.map
        ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app N) = 𝟙 _ := by
    rw [← Functor.map_comp, hA₂]
    simp
  have heQ : (α.naturality gg.op.toLoc).inv.toNatTrans.app
        ((F.map f₂.op.toLoc).toFunctor.obj N) ≫
      (α.naturality gg.op.toLoc).hom.toNatTrans.app
        ((F.map f₂.op.toLoc).toFunctor.obj N) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, (α.naturality gg.op.toLoc).inv_hom_id, Cat.Hom₂.id_app]
  have hC₂ : (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app
        ((α.app (U X₂)).toFunctor.obj N) ≫
      (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app
        ((α.app (U X₂)).toFunctor.obj N) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv_hom_id,
      Cat.Hom₂.id_app]
  have hW : (α.naturality gg.op.toLoc).inv.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫
      (α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N) ≫
      (α.naturality gf₂.op.toLoc).hom.toNatTrans.app N =
      (G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N) ≫
      (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N) := by
    apply (cancel_mono ((G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N))).mp
    calc (((α.naturality gg.op.toLoc).inv.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫
          (α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N) ≫
          (α.naturality gf₂.op.toLoc).hom.toNatTrans.app N) ≫ (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N))
        = ((α.naturality gg.op.toLoc).inv.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ (α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N)) ≫ ((α.naturality gf₂.op.toLoc).hom.toNatTrans.app N ≫ (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N)) := by simp only [Category.assoc]
      _ = ((α.naturality gg.op.toLoc).inv.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ (α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N)) ≫ ((α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app N) ≫ ((α.naturality gg.op.toLoc).hom.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ (G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N))) := by rw [key₂]
      _ = ((α.naturality gg.op.toLoc).inv.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ ((α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app N) ≫ (α.app (U Y')).toFunctor.map ((F.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app N))) ≫ ((α.naturality gg.op.toLoc).hom.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ (G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N)) := by simp only [Category.assoc]
      _ = (α.naturality gg.op.toLoc).inv.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ ((α.naturality gg.op.toLoc).hom.toNatTrans.app ((F.map f₂.op.toLoc).toFunctor.obj N) ≫ (G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N)) := by rw [hmapA₂]; simp
      _ = (G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N) := by rw [← Category.assoc, heQ, Category.id_comp]
      _ = (G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N) ≫ ((G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N) ≫ (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N)) := by rw [hC₂]; simp
      _ = ((G.map gg.op.toLoc).toFunctor.map ((α.naturality f₂.op.toLoc).hom.toNatTrans.app N) ≫ (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).inv.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N)) ≫ (G.mapComp' f₂.op.toLoc gg.op.toLoc gf₂.op.toLoc hφ₂).hom.toNatTrans.app ((α.app (U X₂)).toFunctor.obj N) := by rw [Category.assoc]
  slice_lhs 1 2 => rw [← key₁]
  slice_lhs 3 4 => rw [← keyQ]
  slice_lhs 4 6 => rw [hW]

end LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual