import tmp.sheaf.xif.paper.S2076IsoCommaTwoPullbackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2074IsoCommaTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2076IsoCommaTwoPullbackActual

universe u

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

noncomputable def hConeAt (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U) :=
  (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ↥(c.W.obj U)).obj (h.app U).toFunctor

noncomputable def S2096FibreIsoOfConeIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (e : Iso (hConeAt (f := f) (g := g) c h U) (gConeAt (f := f) (g := g) c U)) :
    Iso (h.app U).toFunctor (gLiftApp (f := f) (g := g) c U) :=
  (S1893LiftIsoOfConeIso (f.map.app U).toFunctor (g.map.app U).toFunctor e).symm

variable (c : S2074GeneralCone f g)
  (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
  (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
  (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
  (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)

theorem eqToHom_self_eq_id {C : Type u} [Category C] {X : C} (h : X = X) :
    eqToHom h = 𝟙 X := by
  rw [Subsingleton.elim h rfl]
  simp

noncomputable def strongTransAppIso {W T : EtaleStackPseudofunctor S1726K}
    {F G : Pseudofunctor.StrongTrans W T}
    (e : Iso F G) (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    F.app U ≅ G.app U where
  hom := e.hom.as.app U
  inv := e.inv.as.app U
  hom_inv_id := by
    have h := congrArg (fun m => m.as.app U) e.hom_inv_id
    exact h
  inv_hom_id := by
    have h := congrArg (fun m => m.as.app U) e.inv_hom_id
    exact h

noncomputable def hConeToA (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (hConeAt (f := f) (g := g) c h U).toA ≅ (gConeAt (f := f) (g := g) c U).toA :=
  Cat.Hom.toNatIso (strongTransAppIso (W := c.W) (T := A.source.fiber)
    (F := Pseudofunctor.StrongTrans.vcomp h (toA f g)) (G := c.toA) eX U)

noncomputable def hConeToB (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (hConeAt (f := f) (g := g) c h U).toB ≅ (gConeAt (f := f) (g := g) c U).toB :=
  Cat.Hom.toNatIso (strongTransAppIso (W := c.W) (T := B.source.fiber)
    (F := Pseudofunctor.StrongTrans.vcomp h (toB f g)) (G := c.toB) eY U)

#print strongTransAppIso
#check Pseudofunctor.StrongTrans.vcomp
#check (Pseudofunctor.StrongTrans.vcomp h (toA f g))
#check hConeToA
#check hConeToB
def S2096ProjectionCompat (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Prop :=
  Functor.whiskerRight (hConeToA (f := f) (g := g) c h eX U).hom
      (f.map.app U).toFunctor ≫ (gConeAt (f := f) (g := g) c U).commutes.hom =
    (hConeAt (f := f) (g := g) c h U).commutes.hom ≫
      Functor.whiskerRight (hConeToB (f := f) (g := g) c h eY U).hom
        (g.map.app U).toFunctor

noncomputable def hConeHomOfProjections (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    S1893Cone.Hom (hConeAt (f := f) (g := g) c h U) (gConeAt (f := f) (g := g) c U) :=
  ⟨((hConeToA (f := f) (g := g) c h eX U).hom,
    (hConeToB (f := f) (g := g) c h eY U).hom), hcompat⟩

noncomputable def hConeIsoOfProjections (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Iso (hConeAt (f := f) (g := g) c h U) (gConeAt (f := f) (g := g) c U) := by
  haveI hA : IsIso (hConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat).toA := by
    change IsIso (hConeToA (f := f) (g := g) c h eX U).hom
    infer_instance
  haveI hB : IsIso (hConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat).toB := by
    change IsIso (hConeToB (f := f) (g := g) c h eY U).hom
    infer_instance
  haveI hIso : IsIso (C := S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) (hConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat) := coneHom_isIso (m := hConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat)
  exact asIso (hConeHomOfProjections (f := f) (g := g) c h eX eY U hcompat)

noncomputable def S2096FibreIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Iso (h.app U).toFunctor (gLiftApp (f := f) (g := g) c U) :=
  S1893LiftUniq (f.map.app U).toFunctor (g.map.app U).toFunctor
    (hConeIsoOfProjections (f := f) (g := g) c h eX eY U hcompat)

theorem test_lift_iso_toA (c : S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) :
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor c).hom).toA =
      𝟙 c.toA := rfl

theorem test_lift_iso_symm_toA (c : S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) :
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor c).symm.hom).toA =
      𝟙 c.toA := rfl

theorem vcomp_h_toA_naturality_apply (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp h (toA f g)).naturality φ).hom.toNatTrans.app x =
      (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((h.naturality φ).hom.toNatTrans.app x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom, Pseudofunctor.StrongTrans.toOplax, toA,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app]
  simp
  erw [Category.comp_id, Category.id_comp]
  rfl

theorem vcomp_h_toB_naturality_apply (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (x : ↑(c.W.obj U)) :
    ((Pseudofunctor.StrongTrans.vcomp h (toB f g)).naturality φ).hom.toNatTrans.app x =
      (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((h.naturality φ).hom.toNatTrans.app x) := by
  simp only [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
    Oplax.StrongTrans.vcomp_naturality_hom, Pseudofunctor.StrongTrans.toOplax, toB,
    Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
    CategoryTheory.Functor.toCatHom_toFunctor, Cat.Hom₂.comp_app]
  simp
  erw [Category.comp_id, Category.id_comp]
  rfl

theorem test_lift_iso_symm_toB (c : S1893Cone (f.map.app U).toFunctor (g.map.app U).toFunctor ↥(c.W.obj U)) :
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor c).symm.hom).toB =
      𝟙 c.toB := rfl

theorem S2096FibreIso_mapIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
      ↥(c.W.obj U)).mapIso (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat) =
      (hConeIsoOfProjections (f := f) (g := g) c h eX eY U hcompat).trans
        (S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor
          (gConeAt (f := f) (g := g) c U)).symm := by
  dsimp [S2096FibreIso, S1893LiftUniq]
  exact (Functor.FullyFaithful.isoEquiv
    (Functor.FullyFaithful.ofFullyFaithful
      (S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
        ↥(c.W.obj U)))).apply_symm_apply _

theorem S2096FibreIso_hom_fst (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Functor.whiskerRight (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom
        (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor) =
      (hConeToA (f := f) (g := g) c h eX U).hom := by
  have hmap := S2096FibreIso_mapIso (f := f) (g := g) c h eX eY U hcompat
  have hproj := congrArg (fun m => m.hom.toA) hmap
  change ((S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ↥(c.W.obj U)).mapIso (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat)).hom.toA =
      (hConeToA (f := f) (g := g) c h eX U).hom
  rw [hproj]
  change (hConeToA (f := f) (g := g) c h eX U).hom ≫
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor
      (gConeAt (f := f) (g := g) c U)).symm.hom).toA = _
  rw [test_lift_iso_symm_toA]
  simp

theorem S2096FibreIso_hom_snd (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Functor.whiskerRight (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom
        (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor) =
      (hConeToB (f := f) (g := g) c h eY U).hom := by
  have hmap := S2096FibreIso_mapIso (f := f) (g := g) c h eX eY U hcompat
  have hproj := congrArg (fun m => m.hom.toB) hmap
  change ((S1893ComparisonFunctor (f.map.app U).toFunctor (g.map.app U).toFunctor
    ↥(c.W.obj U)).mapIso (S2096FibreIso (f := f) (g := g) c h eX eY U hcompat)).hom.toB =
      (hConeToB (f := f) (g := g) c h eY U).hom
  rw [hproj]
  change (hConeToB (f := f) (g := g) c h eY U).hom ≫
    ((S1893ComparisonFunctor_obj_lift_iso (f.map.app U).toFunctor (g.map.app U).toFunctor
      (gConeAt (f := f) (g := g) c U)).symm.hom).toB = _
  rw [test_lift_iso_symm_toB]
  simp

theorem S1890IsoCommaMap_fst_app {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) {X Y : ↑(S1890IsoCommaObj f g U)} (y : X ⟶ Y) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y) =
      (A.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := by
  calc
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y)
        = ((S1890IsoCommaMap f g φ).toFunctor ⋙
            S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map y := rfl
    _ = ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor) ⋙
          (A.source.fiber.map φ).toFunctor).map y := by
          erw [S1890IsoCommaMap_fst]
    _ = (A.source.fiber.map φ).toFunctor.map
          ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := rfl

theorem S1890IsoCommaMap_snd_app {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) {X Y : ↑(S1890IsoCommaObj f g U)} (y : X ⟶ Y) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y) =
      (B.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := by
  calc
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map y)
        = ((S1890IsoCommaMap f g φ).toFunctor ⋙
            S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map y := rfl
    _ = ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor) ⋙
          (B.source.fiber.map φ).toFunctor).map y := by
          erw [S1890IsoCommaMap_snd]
    _ = (B.source.fiber.map φ).toFunctor.map
          ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map y) := rfl

theorem S2096FibreIso_hom_fst_app (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom.app y) =
      (hConeToA (f := f) (g := g) c h eX U).hom.app y := by
  simpa only [Functor.whiskerRight_app] using
    congrArg (fun α => α.app y)
      (S2096FibreIso_hom_fst (f := f) (g := g) c h eX eY U hcompat)

theorem S2096FibreIso_hom_snd_app (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (hcompat : S2096ProjectionCompat (f := f) (g := g) c h eX eY U)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((S2096FibreIso (f := f) (g := g) c h eX eY U hcompat).hom.app y) =
      (hConeToB (f := f) (g := g) c h eY U).hom.app y := by
  simpa only [Functor.whiskerRight_app] using
    congrArg (fun α => α.app y)
      (S2096FibreIso_hom_snd (f := f) (g := g) c h eX eY U hcompat)

theorem gLiftNat_hom_fst_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((gLiftNat (f := f) (g := g) c φ).hom.app y) =
      (c.toA.naturality φ).hom.toNatTrans.app y := by
  simpa only [Functor.whiskerRight_app, gLiftNatConeA] using
    congrArg (fun α => α.app y) (gLiftNat_hom_fst (f := f) (g := g) c φ)

theorem gLiftNat_hom_snd_app (c : S2074GeneralCone f g)
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    (y : ↑(c.W.obj U)) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((gLiftNat (f := f) (g := g) c φ).hom.app y) =
      (c.toB.naturality φ).hom.toNatTrans.app y := by
  simpa only [Functor.whiskerRight_app, gLiftNatConeB] using
    congrArg (fun α => α.app y) (gLiftNat_hom_snd (f := f) (g := g) c φ)


noncomputable def S2096SiteIso (c : S2074GeneralCone f g)
    (h : Pseudofunctor.StrongTrans c.W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toA)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toB)
    (hcompat : ∀ U, S2096ProjectionCompat (f := f) (g := g) c h eX eY U) :
    Iso h (gLiftSite (f := f) (g := g) c) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun U => Cat.Hom.isoMk (S2096FibreIso (f := f) (g := g) c h eX eY U (hcompat U)))
    (by
      intro U V φ
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext x
      apply S1836IsoComma_hom_ext (f.map.app V).toFunctor (g.map.app V).toFunctor
      · simp only [NatTrans.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans,
          Cat.whiskerRight_toNatTrans, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
          CategoryTheory.Functor.toCatHom_toFunctor, gLiftSite, sitePseudofunctor_map,
          S2096FibreIso_hom_fst_app, gLiftNat_hom_fst_app,
          S1890IsoCommaMap_fst_app, Functor.map_comp]
        rw [← vcomp_h_toA_naturality_apply]
        have hX := congrArg (fun al => al.toNatTrans.app x) (eX.hom.as.naturality φ)
        simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
          Functor.whiskerLeft_app, Functor.whiskerRight_app] at hX
        simpa [hConeToA, strongTransAppIso] using hX
      · simp only [NatTrans.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans,
          Cat.whiskerRight_toNatTrans, Functor.whiskerLeft_app, Functor.whiskerRight_app,
          Cat.Hom.isoMk, Cat.Hom.toNatIso, NatTrans.toCatHom₂_toNatTrans,
          CategoryTheory.Functor.toCatHom_toFunctor, gLiftSite, sitePseudofunctor_map,
          S2096FibreIso_hom_snd_app, gLiftNat_hom_snd_app,
          S1890IsoCommaMap_snd_app, Functor.map_comp]
        rw [← vcomp_h_toB_naturality_apply]
        have hY := congrArg (fun al => al.toNatTrans.app x) (eY.hom.as.naturality φ)
        simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
          Functor.whiskerLeft_app, Functor.whiskerRight_app] at hY
        simpa [hConeToB, strongTransAppIso] using hY)

noncomputable def S2096LiftUniq_of_projectionCompat
    {W : EtaleStackPseudofunctor S1726K}
    (c : (S2076Square (f := f) (g := g)).Cone W)
    (h : Pseudofunctor.StrongTrans W (sitePseudofunctor f g))
    (eX : Iso (Pseudofunctor.StrongTrans.vcomp h (toA f g)) c.toX)
    (eY : Iso (Pseudofunctor.StrongTrans.vcomp h (toB f g)) c.toY)
    (hcompat : ∀ U, S2096ProjectionCompat (f := f) (g := g)
      (S2076ConeToGeneral (f := f) (g := g) c) h eX eY U) :
    Iso h ((S2076Witness (f := f) (g := g)).lift W c) :=
  S2096SiteIso (f := f) (g := g) (S2076ConeToGeneral (f := f) (g := g) c)
    h eX eY hcompat

#check hConeAt
#check S2096FibreIsoOfConeIso
#check hConeHomOfProjections
#check hConeIsoOfProjections
#check S2096FibreIso

end LeanFormal.IUT.XiFPaper.S2101SiteNaturalityActual

end