import tmp.sheaf.xif.paper.S2084LiftNatIsoActual

/-! # S2085: general liftNatIso projections and liftSite

Adapted from S1985 to arbitrary `S2074GeneralCone`s.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2085GeneralLiftSiteActualAdapted

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
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2078ConeAtLiftAppActual
open LeanFormal.IUT.XiFPaper.S2079GeneralLiftNatActual
open LeanFormal.IUT.XiFPaper.S2084LiftNatIsoActual

universe u
variable {A B C : S1728Cover}
variable (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- First projection of the general liftNatIso. -/
theorem S2085liftNatIso_hom_fst (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Functor.whiskerRight (S2084liftNatIso f g c φ).hom
        (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) =
      S2079LiftNatConeA f g c φ := by
  change ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↑(c.W.obj U)).map (S2084liftNatIso f g c φ).hom).toA =
    S2079LiftNatConeA f g c φ
  dsimp only [S2084liftNatIso]
  simp only [Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage]
  rfl

/-- Second projection of the general liftNatIso. -/
theorem S2085liftNatIso_hom_snd (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Functor.whiskerRight (S2084liftNatIso f g c φ).hom
        (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) =
      S2079LiftNatConeB f g c φ := by
  change ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↑(c.W.obj U)).map (S2084liftNatIso f g c φ).hom).toB =
    S2079LiftNatConeB f g c φ
  dsimp only [S2084liftNatIso]
  simp only [Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage]
  rfl

noncomputable def liftSite (c : S2074GeneralCone f g) :
    Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g) where
  app U := (S2078LiftApp f g c U).toCatHom
  naturality {U V} φ := Cat.Hom.isoMk (S2084liftNatIso f g c φ)
  naturality_naturality := by
    intro U V φ ψ η
    obtain rfl := LocallyDiscrete.eq_of_hom η
    have heta : η = 𝟙 φ := Subsingleton.elim _ _
    rw [heta, PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    rw [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  naturality_id := by
    intro U
    apply Cat.Hom₂.ext
    apply (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
      ↥(c.W.obj U)).map_injective
    apply S1893Cone.Hom.ext
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, CategoryTheory.Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight
          ((S2084liftNatIso f g c (𝟙 U)).hom ≫
            (S2078LiftApp f g c U).toCatHom.toFunctor.whiskerLeft
              ((sitePseudofunctor f g).mapId U).hom.toNatTrans)
          (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x =
        (Functor.whiskerRight
          (Functor.whiskerRight (c.W.mapId U).hom.toNatTrans
              (S2078LiftApp f g c U).toCatHom.toFunctor ≫
            (λ_ (S2078LiftApp f g c U).toCatHom).hom.toNatTrans ≫
              (ρ_ (S2078LiftApp f g c U).toCatHom).inv.toNatTrans)
          (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x
      rw [Functor.whiskerRight_comp, NatTrans.comp_app]
      simp only [S2085liftNatIso_hom_fst]
      rw [Functor.whiskerRight_left]
      rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_twice]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_hom_app, Cat.leftUnitor_inv_app, Cat.rightUnitor_inv_app,
        Category.comp_id, Category.id_comp, siteMapId_fst]
      simp only [Functor.associator]
      erw [Category.id_comp]
      simp only [sitePseudofunctor_mapId]
      rw [siteMapId_fst]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toA.naturality_id U)
      simp only [CategoryTheory.eqToHom_map]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Category.comp_id,
          Category.id_comp, CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, CategoryTheory.Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight
          ((S2084liftNatIso f g c (𝟙 U)).hom ≫
            (S2078LiftApp f g c U).toCatHom.toFunctor.whiskerLeft
              ((sitePseudofunctor f g).mapId U).hom.toNatTrans)
          (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x =
        (Functor.whiskerRight
          (Functor.whiskerRight (c.W.mapId U).hom.toNatTrans
              (S2078LiftApp f g c U).toCatHom.toFunctor ≫
            (λ_ (S2078LiftApp f g c U).toCatHom).hom.toNatTrans ≫
              (ρ_ (S2078LiftApp f g c U).toCatHom).inv.toNatTrans)
          (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor)).app x
      rw [Functor.whiskerRight_comp, NatTrans.comp_app]
      simp only [S2085liftNatIso_hom_snd]
      rw [Functor.whiskerRight_left]
      rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Functor.whiskerRight_twice]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app, Cat.leftUnitor_hom_app,
        Cat.rightUnitor_hom_app, Cat.leftUnitor_inv_app, Cat.rightUnitor_inv_app,
        Category.comp_id, Category.id_comp, siteMapId_snd]
      simp only [Functor.associator]
      erw [Category.id_comp]
      simp only [sitePseudofunctor_mapId]
      rw [siteMapId_snd]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toB.naturality_id U)
      simp only [CategoryTheory.eqToHom_map]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      try erw [Category.id_comp]
      try erw [Category.comp_id]
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Category.comp_id,
          Category.id_comp, CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl
  naturality_comp := by
    intro U V Z φ ψ
    apply Cat.Hom₂.ext
    apply (S1893ComparisonFunctor (f.map.app Z).toFunctor (g.map.app Z).toFunctor
      ↥(c.W.obj U)).map_injective
    apply S1893Cone.Hom.ext
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight _ (S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x =
        (Functor.whiskerRight _ (S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x
      simp only [Functor.whiskerRight_comp, NatTrans.comp_app,
        Functor.whiskerRight_left, Functor.whiskerRight_twice,
        S2085liftNatIso_hom_fst, sitePseudofunctor_mapComp, siteMapComp_fst,
        sitePseudofunctor_map, S1890IsoCommaMap_fst,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app,
        Category.comp_id, Category.id_comp, Functor.associator]
      repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
      have hlast : ((S1890IsoCommaMap f g ψ).toFunctor ⋙
          S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor).map
            ((S2084liftNatIso f g c φ).hom.app x) =
          (A.source.fiber.map ψ).toFunctor.map ((liftNatConeA f g c φ).app x) := by
        change (A.source.fiber.map ψ).toFunctor.map
            ((Functor.whiskerRight (S2084liftNatIso f g c φ).hom
              (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x) = _
        rw [S2085liftNatIso_hom_fst]
      rw [hlast]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toA.naturality_comp φ ψ)
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Cat.associator_hom_app,
          Cat.associator_inv_app, Category.comp_id, Category.id_comp,
          CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl
    · apply NatTrans.ext
      funext x
      simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.isoMk, Cat.Hom.toNatIso,
        NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor]
      dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight _ (S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x =
        (Functor.whiskerRight _ (S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor)).app x
      simp only [Functor.whiskerRight_comp, NatTrans.comp_app,
        Functor.whiskerRight_left, Functor.whiskerRight_twice,
        S2085liftNatIso_hom_snd, sitePseudofunctor_mapComp, siteMapComp_snd,
        sitePseudofunctor_map, S1890IsoCommaMap_snd,
        Functor.whiskerLeft_app, Functor.whiskerRight_app,
        Cat.associator_hom_app, Cat.associator_inv_app,
        Category.comp_id, Category.id_comp, Functor.associator]
      repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
      have hlast : ((S1890IsoCommaMap f g ψ).toFunctor ⋙
          S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor).map
            ((S2084liftNatIso f g c φ).hom.app x) =
          (B.source.fiber.map ψ).toFunctor.map ((liftNatConeB f g c φ).app x) := by
        change (B.source.fiber.map ψ).toFunctor.map
            ((Functor.whiskerRight (S2084liftNatIso f g c φ).hom
              (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x) = _
        rw [S2085liftNatIso_hom_snd]
      rw [hlast]
      have h := congrArg (fun m => m.toNatTrans.app x) (c.toB.naturality_comp φ ψ)
      convert h using 1
      · rfl
      · rfl
      · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
          Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Cat.associator_hom_app,
          Cat.associator_inv_app, Category.comp_id, Category.id_comp,
          CategoryTheory.eqToHom_map, eqToHom_refl]
        rfl


theorem vcomp_lift_toA_naturality_hom (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    ((Pseudofunctor.StrongTrans.vcomp (liftSite (f := f) (g := g) c) (toA f g)).naturality φ).hom =
      (c.toA.naturality φ).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, toA,
    Cat.Hom.toNatIso, Cat.Hom.isoMk, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp only [liftSite, Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  rw [← Functor.whiskerRight_app]
  simp only [S2085liftNatIso_hom_fst, liftNatConeA, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id]
  change (Functor.whiskerRight (S2084liftNatIso f g c φ).hom
      (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x =
    (c.toA.naturality φ).hom.toNatTrans.app x
  rw [S2085liftNatIso_hom_fst]
  rfl


theorem vcomp_lift_toB_naturality_hom (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    ((Pseudofunctor.StrongTrans.vcomp (liftSite (f := f) (g := g) c) (toB f g)).naturality φ).hom =
      (c.toB.naturality φ).hom := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, toB,
    Cat.Hom.toNatIso, Cat.Hom.isoMk, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp only [liftSite, Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  rw [← Functor.whiskerRight_app]
  simp only [S2085liftNatIso_hom_snd, liftNatConeA, eqToHom_refl, Category.id_comp,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id]
  change (Functor.whiskerRight (S2084liftNatIso f g c φ).hom
      (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor)).app x =
    (c.toB.naturality φ).hom.toNatTrans.app x
  rw [S2085liftNatIso_hom_snd]
  rfl



#print axioms S2085liftSite

end LeanFormal.IUT.XiFPaper.S2085GeneralLiftSiteActualAdapted

end
