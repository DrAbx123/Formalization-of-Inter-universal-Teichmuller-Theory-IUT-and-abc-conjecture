import tmp.sheaf.xif.paper.S1955AssembleCDActual

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1832ActualCoverPullbacksActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1985Probe

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

theorem vcomp_toA_naturality_apply {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp c.toA.map f.map).naturality φ).hom.toNatTrans.app x =
      (f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
        (S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, S1864SiteComparisonLeft,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp
  erw [Category.id_comp]

theorem vcomp_toB_naturality_apply {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp c.toB.map g.map).naturality φ).hom.toNatTrans.app x =
      (g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) ≫
        (S1864SiteComparisonRight g φ).inv.app ((c.toB.map.app U).toFunctor.obj x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom,
    Pseudofunctor.StrongTrans.toOplax, S1864SiteComparisonRight,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app,
    Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app,
    Cat.leftUnitor_hom_app, Cat.leftUnitor_inv_app,
    Cat.rightUnitor_hom_app, Cat.rightUnitor_inv_app,
    Cat.Hom₂.eqToHom_toNatTrans, Cat.eqToHom_app,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, eqToIso.hom,
    Category.comp_id, Category.id_comp]
  simp
  erw [Category.id_comp]

noncomputable def liftNatConeA {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toA.map.naturality φ).hom.toNatTrans

noncomputable def liftNatConeB {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    (((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) ⟶
      ((liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) ⋙
        S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) :=
  (c.toB.map.naturality φ).hom.toNatTrans

theorem cone1_commutes_app {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          ((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V)).commutes.hom.app x =
      (c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((liftApp (f := f) (g := g) c V).obj
    ((W.source.fiber.map φ).toFunctor.obj x)).obj.hom = _
  simp only [liftApp]
  rw [S1893Lift_structure]
  rfl

theorem cone2_commutes_app {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)).commutes.hom.app x =
      (S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) ≫
        (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
          (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x) := by
  rw [S1893ComparisonFunctor_obj_commutes_hom_app, S1836IsoCommaNatIso_hom_app]
  change ((S1864IsoCommaRestrict (A.source.fiber.map φ).toFunctor
      (B.source.fiber.map φ).toFunctor (C.source.fiber.map φ).toFunctor
      (S1864SiteComparisonLeft f φ) (S1864SiteComparisonRight g φ)).obj
        ((S1893Lift (f.map.app U).toFunctor (g.map.app U).toFunctor
          (coneAt (f := f) (g := g) c U)).obj x)).obj.hom = _
  rw [S1864IsoCommaRestrict_obj_hom]
  rw [S1893Lift_structure]
  rfl

theorem liftCone_compat {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(W.source.fiber.obj U)) :
    (f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
        ((S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) ≫
          (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
            (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x)) =
      (c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) ≫
        (g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) := by
  have h := congrArg (fun m => m.toNatTrans.app x) (c.commutes.hom.as.naturality φ)
  simp only [Functor.whiskerRight_app, NatTrans.toCatHom₂_toNatTrans,
      Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
  rw [vcomp_toA_naturality_apply (f := f) (g := g) c φ x,
      vcomp_toB_naturality_apply (f := f) (g := g) c φ x] at h
  calc
    (f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
        ((S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x) ≫
          (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x) ≫
            (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x))
        = ((((f.map.app V).toFunctor.map ((c.toA.map.naturality φ).hom.toNatTrans.app x) ≫
            (S1864SiteComparisonLeft f φ).hom.app ((c.toA.map.app U).toFunctor.obj x)) ≫
              (C.source.fiber.map φ).toFunctor.map ((c.commutes.hom.as.app U).toNatTrans.app x)) ≫
                (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x)) := by
          simp only [Category.assoc]
    _ = ((c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) ≫
            ((g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) ≫
              (S1864SiteComparisonRight g φ).inv.app ((c.toB.map.app U).toFunctor.obj x))) ≫
                  (S1864SiteComparisonRight g φ).hom.app ((c.toB.map.app U).toFunctor.obj x) := by
          rw [← h]
    _ = (c.commutes.hom.as.app V).toNatTrans.app ((W.source.fiber.map φ).toFunctor.obj x) ≫
          (g.map.app V).toFunctor.map ((c.toB.map.naturality φ).hom.toNatTrans.app x) := by
          simp only [Category.assoc, Iso.inv_hom_id_app]
          erw [Category.comp_id]


/-! ## Cone hom and comparison -/

noncomputable def liftConeHomForward {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    S1893Cone.Hom
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          ((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) :=
  ⟨(liftNatConeA (f := f) (g := g) c φ, liftNatConeB (f := f) (g := g) c φ), by
    apply NatTrans.ext
    funext x
    dsimp only
    simp only [NatTrans.comp_app, Functor.whiskerRight_app]
    rw [cone1_commutes_app, cone2_commutes_app]
    dsimp only [liftNatConeA, liftNatConeB]
    exact liftCone_compat f g c φ x⟩


universe u

theorem coneHom_isIso {A' B' C' X : Type u} [Category.{u, u} A'] [Category.{u, u} B']
    [Category.{u, u} C'] [Category.{u, u} X] {L : A' ⥤ C'} {R : B' ⥤ C'}
    {c₁ c₂ : S1893Cone L R X} (m : S1893Cone.Hom c₁ c₂)
    [IsIso m.toA] [IsIso m.toB] : IsIso (C := S1893Cone L R X) m := by
  let invA : c₂.toA ⟶ c₁.toA := inv m.toA
  let invB : c₂.toB ⟶ c₁.toB := inv m.toB
  have hα : Functor.whiskerRight invA L = inv (Functor.whiskerRight m.toA L) := by
    dsimp [invA]
    simp
  have hβ : Functor.whiskerRight invB R = inv (Functor.whiskerRight m.toB R) := by
    dsimp [invB]
    simp
  have hcomp : Functor.whiskerRight invA L ≫ c₁.commutes.hom =
      c₂.commutes.hom ≫ Functor.whiskerRight invB R := by
    have hm := m.2
    have hf : c₁.commutes.hom = Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
        inv (Functor.whiskerRight m.toB R) := by
      calc
        c₁.commutes.hom = (c₁.commutes.hom ≫ Functor.whiskerRight m.toB R) ≫
            inv (Functor.whiskerRight m.toB R) := by
          rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        _ = (Functor.whiskerRight m.toA L ≫ c₂.commutes.hom) ≫
            inv (Functor.whiskerRight m.toB R) := by rw [← hm]
        _ = Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
            inv (Functor.whiskerRight m.toB R) := by simp only [Category.assoc]
    rw [hα, hβ]
    calc
      inv (Functor.whiskerRight m.toA L) ≫ c₁.commutes.hom =
          inv (Functor.whiskerRight m.toA L) ≫
            (Functor.whiskerRight m.toA L ≫ c₂.commutes.hom ≫
              inv (Functor.whiskerRight m.toB R)) := by rw [hf]
      _ = c₂.commutes.hom ≫ inv (Functor.whiskerRight m.toB R) := by
        simp only [← Category.assoc]
        rw [← hα, ← Functor.whiskerRight_comp]
        rw [show invA ≫ m.toA = 𝟙 c₂.toA by dsimp [invA]; simp]
        rw [Functor.whiskerRight_id']
        simp
  let inv' : S1893Cone.Hom c₂ c₁ := ⟨(invA, invB), hcomp⟩
  refine ⟨inv', ?_, ?_⟩
  · apply S1893Cone.Hom.ext
    · change m.toA ≫ invA = 𝟙 c₁.toA
      dsimp [invA]
      simp
    · change m.toB ≫ invB = 𝟙 c₁.toB
      dsimp [invB]
      simp
  · apply S1893Cone.Hom.ext
    · change invA ≫ m.toA = 𝟙 c₂.toA
      dsimp [invA]
      simp
    · change invB ≫ m.toB = 𝟙 c₂.toB
      dsimp [invB]
      simp

noncomputable def liftConeIso {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Iso
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          ((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V))
      ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)).obj
          (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor)) := by
  haveI hA : IsIso (liftConeHomForward (f := f) (g := g) c φ).toA := by
    change IsIso ((c.toA.map.naturality φ).hom.toNatTrans)
    infer_instance
  haveI hB : IsIso (liftConeHomForward (f := f) (g := g) c φ).toB := by
    change IsIso ((c.toB.map.naturality φ).hom.toNatTrans)
    infer_instance
  letI : IsIso (C := S1893Cone (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↥(W.source.fiber.obj U)) (liftConeHomForward (f := f) (g := g) c φ) :=
    coneHom_isIso (m := liftConeHomForward (f := f) (g := g) c φ)
  exact asIso (liftConeHomForward (f := f) (g := g) c φ)

noncomputable def liftNatIso {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Iso (((W.source.fiber.map φ).toFunctor ⋙ liftApp (f := f) (g := g) c V))
      (liftApp (f := f) (g := g) c U ⋙ (S1890IsoCommaMap f g φ).toFunctor) :=
  Functor.FullyFaithful.preimageIso
    (Functor.FullyFaithful.ofFullyFaithful
      (S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
        ↥(W.source.fiber.obj U)))
    (liftConeIso (f := f) (g := g) c φ)

theorem liftNatIso_hom_fst {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Functor.whiskerRight (liftNatIso (f := f) (g := g) c φ).hom
        (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor) =
      liftNatConeA (f := f) (g := g) c φ := by
  change ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↥(W.source.fiber.obj U)).map (liftNatIso (f := f) (g := g) c φ).hom).toA =
    liftNatConeA (f := f) (g := g) c φ
  dsimp only [liftNatIso]
  simp only [Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage]
  rfl

theorem liftNatIso_hom_snd {W : S1728Cover} (c : S1832Bicone f g W)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) :
    Functor.whiskerRight (liftNatIso (f := f) (g := g) c φ).hom
        (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor) =
      liftNatConeB (f := f) (g := g) c φ := by
  change ((S1893ComparisonFunctor (f.map.app V).toFunctor (g.map.app V).toFunctor
      ↥(W.source.fiber.obj U)).map (liftNatIso (f := f) (g := g) c φ).hom).toB =
    liftNatConeB (f := f) (g := g) c φ
  dsimp only [liftNatIso]
  simp only [Functor.FullyFaithful.preimageIso, Functor.FullyFaithful.map_preimage]
  rfl


noncomputable def liftSite {W : S1728Cover} (c : S1832Bicone f g W) :
    Pseudofunctor.StrongTrans W.source.fiber (sitePseudofunctor f g) where
  app U := (liftApp (f := f) (g := g) c U).toCatHom
  naturality {U V} φ := Cat.Hom.isoMk (liftNatIso (f := f) (g := g) c φ)
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
      ↥(W.source.fiber.obj U)).map_injective
    apply S1893Cone.Hom.ext
    · dsimp only [S1893ComparisonFunctor]
      change (Functor.whiskerRight
          (((Cat.Hom.isoMk (liftNatIso f g c (𝟙 U))).hom ≫
            ((liftApp f g c U).toCatHom ◁ ((sitePseudofunctor f g).mapId U).hom)).toNatTrans)
          (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor)) =
        (Functor.whiskerRight
          (((W.source.fiber.mapId U).hom ▷ (liftApp f g c U).toCatHom) ≫
            (λ_ (liftApp f g c U).toCatHom).hom ≫
              (ρ_ (liftApp f g c U).toCatHom).inv).toNatTrans
          (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor))
        simp only [Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.Hom.toNatTrans_id, Cat.Hom.isoMk,
        Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor,
        Functor.whiskerRight_comp, Functor.whiskerRight_left, Functor.whiskerRight_twice,
        sitePseudofunctor_mapId, siteMapId_fst,
        Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_inv_toNatTrans,
        Functor.associator, Category.comp_id, Category.id_comp]
      trace_state
      sorry

  naturality_comp := by
    intro U V W φ ψ
    sorry

end LeanFormal.IUT.XiFPaper.S1985Probe