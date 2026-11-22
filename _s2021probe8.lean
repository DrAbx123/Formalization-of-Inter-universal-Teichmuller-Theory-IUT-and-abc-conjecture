import tmp.sheaf.xif.paper.S2012EffectivityComparisonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option pp.proofs false

namespace Probe

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1998IsoCommaPrestackActual
open LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual
open LeanFormal.IUT.XiFPaper.S2012EffectivityComparisonActual

abbrev K := S1726K
abbrev Site := SchemeOverField K

abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

variable {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
  (α : Pseudofunctor.StrongTrans F G) {S : Site} {R : Sieve S} (M : F.obj (U S))

/-- Core comm identity for the push comparison. -/
theorem core
    {Y : Site} (q : Y ⟶ S) {i₁ i₂ : R.arrows.category}
    (f₁ : Y ⟶ i₁.obj.left) (f₂ : Y ⟶ i₂.obj.left)
    (hf₁ : f₁ ≫ i₁.obj.hom = q) (hf₂ : f₂ ≫ i₂.obj.hom = q)
    (p₁ : i₁.obj.hom.op.toLoc ≫ f₁.op.toLoc = q.op.toLoc)
    (p₂ : i₂.obj.hom.op.toLoc ≫ f₂.op.toLoc = q.op.toLoc) :
    (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫
      (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) ≫
        (α.app (U Y)).toFunctor.map (((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M)) ≫
          (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) =
      (((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M))) ≫
        (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by
  have h₁ := S2012natCompInvApp_comp' (F := F) (G := G) (α := α)
    (φ := i₁.obj.hom.op.toLoc) (ψ := f₁.op.toLoc) (χ := q.op.toLoc) p₁ (x := M)
  have h₂ := S2012natCompHomApp_comp' (F := F) (G := G) (α := α)
    (φ := i₂.obj.hom.op.toLoc) (ψ := f₂.op.toLoc) (χ := q.op.toLoc) p₂ (x := M)
  have hGC1 : ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, (G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv_hom_id, Cat.Hom₂.id_app]
  have hA1P1 : (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) := by
    rw [← h₁, ← Category.assoc, hGC1, Category.id_comp]
  have hA1P1p : (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) =
      ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)) hA1P1
  have hpF1 : (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) = (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) :=
    Iso.hom_inv_id_assoc ((α.app (U Y)).toFunctor.mapIso ((Cat.Hom.toNatIso (F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁)).app M)) ((α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M))
  have h2a : ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) =
      ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := by
    simpa only [Category.assoc] using congrArg (fun m => ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ m) hpF1
  have hGmBA : (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).hom.toNatTrans.app M) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) = 𝟙 _ := Iso.hom_inv_id ((G.map f₂.op.toLoc).toFunctor.mapIso ((Cat.Hom.toNatIso (α.naturality (i₂.obj.hom.op.toLoc))).app M))
  have hZinvZhom : (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.naturality q.op.toLoc).hom.toNatTrans.app M = 𝟙 _ := Iso.inv_hom_id ((Cat.Hom.toNatIso (α.naturality q.op.toLoc)).app M)
  have hZ2 : (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) = ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by
    have h1' : (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) = (α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by
      calc (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)
          = (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) ≫ ((G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).hom.toNatTrans.app M) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M)) := by erw [hGmBA, Category.comp_id]
        _ = ((α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).hom.toNatTrans.app M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by simp only [Category.assoc]
        _ = ((α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M))) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by rw [← h₂]
        _ = (α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by simp only [Category.assoc]
    calc (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)
        = (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ ((α.naturality q.op.toLoc).hom.toNatTrans.app M ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M)) := by rw [h1']
      _ = ((α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.naturality q.op.toLoc).hom.toNatTrans.app M) ≫ ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by simp only [Category.assoc]
      _ = ((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M) := by rw [hZinvZhom, Category.id_comp]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  calc (G.map f₁.op.toLoc).toFunctor.map ((α.naturality (i₁.obj.hom.op.toLoc)).inv.toNatTrans.app M) ≫ (α.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map (i₁.obj.hom.op.toLoc)).toFunctor.obj M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M)
      = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).hom.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app M) ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := hA1P1p
    _ = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (α.naturality q.op.toLoc).inv.toNatTrans.app M ≫ (α.app (U Y)).toFunctor.map ((F.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app M) ≫ (α.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map (i₂.obj.hom.op.toLoc)).toFunctor.obj M) := h2a
    _ = ((G.mapComp' (i₁.obj.hom.op.toLoc) f₁.op.toLoc q.op.toLoc p₁).inv.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (((G.mapComp' (i₂.obj.hom.op.toLoc) f₂.op.toLoc q.op.toLoc p₂).hom.toNatTrans.app ((α.app (U S)).toFunctor.obj M)) ≫ (G.map f₂.op.toLoc).toFunctor.map ((α.naturality (i₂.obj.hom.op.toLoc)).inv.toNatTrans.app M)) := by rw [hZ2]

example :
    (Pseudofunctor.toDescentData G (fun (i : R.arrows.category) => i.obj.hom)).obj
        ((α.app (U S)).toFunctor.obj M) ≅
      S2004PushDescentData (R := R) α
        ((Pseudofunctor.toDescentData F (fun (i : R.arrows.category) => i.obj.hom)).obj M) :=
  Pseudofunctor.DescentData.isoMk
    (fun i => (Cat.Hom.toNatIso (α.naturality ((i.obj.hom).op.toLoc))).symm.app M)
    (by
      intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      dsimp only [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
        S2004PushDescentData]
      rw [S2012toNatIso_symm_app_hom, S2012toNatIso_symm_app_hom]
      exact core α M q f₁ f₂ hf₁ hf₂ _ _)

end Probe
