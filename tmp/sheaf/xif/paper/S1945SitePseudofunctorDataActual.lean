/-
# S1945: the actual iso-comma site pseudofunctor data -- S1864 (a) closed

## Context

S1935 reduced S1864 (a) (the iso-comma site pseudofunctor for a cospan of actual
finite-etale cover maps f : A -> C, g : B -> C) to the existence of comparison
data mapComp, mapId together with the three pseudofunctor coherence equations,
and recorded this as S1935RemainingSitePseudofunctor f g.  It also proved the
three site-level pasting identities S1890SiteCompF, S1890SiteCompG,
S1890SiteIdG, and diagnosed a possible direction mismatch for the composite
square: S1890CompSquare consumes beta_1.hom, beta_2.hom, while
S1890SiteCompG is stated in the inverse-naturality direction.

## What is done here

1.  The hom-direction g-side pasting identity (siteCompGHom).  It is proved from
    S1935's natCompHomApp_comp (the componentwise
    Pseudofunctor.StrongTrans.naturality_comp_hom with the trailing inverse
    comparison cancelled), i.e. it is the mirror of the f-side identity
    S1890SiteCompF with g in place of f.

2.  The direction analysis is settled.  The second comparison of
    S1864CoverIsoCommaRestrict is
    S1864SiteComparisonRight g phi = (Cat.Hom.toNatIso (g.map.naturality phi)).symm,
    so S1890CompSquare consumes beta.hom = (g.map.naturality phi).inv, which is
    exactly the inverse-naturality direction of S1890SiteCompG.  Hence the
    composite square siteCompSquare is proved from the three pasting identities
    S1890SiteCompF, S1890SiteCompC, S1890SiteCompG (no hom-direction identity is
    needed for it); the requested hom-direction identity siteCompGHom is
    nevertheless supplied and proved above.  The identity square siteIdSquare is
    proved from S1890SiteIdF, the C-side mapId naturality, and S1890SiteIdG.

3.  The concrete comparison data.  siteMapComp is the general restriction
    comparison S1890RestrictCompIso applied to the site data, and siteMapId is
    S1890RestrictIdIso applied to the site data.  Their components are computed
    explicitly (siteMapComp_fst, siteMapComp_snd, siteMapComp_inv_fst,
    siteMapComp_inv_snd, siteMapId_fst, siteMapId_snd, ...).

4.  The three coherence equations (siteCoherence_assoc,
    siteCoherence_leftUnitor, siteCoherence_rightUnitor).  Each is proved by
    reducing, along the two joint-faithful iso-comma projections
    (S1836IsoComma_hom_ext), to the corresponding pseudofunctor coherence of
    A.source.fiber and B.source.fiber (Pseudofunctor.map2_associator,
    map2_left_unitor, map2_right_unitor) and to the strictness of Cat.  The
    residual right-hand side eqToHom (by simp) is identified with the map2 of the
    locally discrete associator / unitor via Bicategory.Strict.associator_eqToIso
    and PrelaxFunctor.map2_eqToHom.  No coherence is assumed or faked.

5.  The site pseudofunctor (sitePseudofunctor).  It is built with
    pseudofunctorOfIsLocallyDiscrete from S1890IsoCommaObj, S1890IsoCommaMap,
    siteMapId, siteMapComp and the three coherence laws.  Its value at U is
    definitionally the iso-comma category S1836IsoComma (f.map.app U) (g.map.app U),
    and its 1-cell at phi is definitionally S1890IsoCommaMap f g phi (with the
    strict projection compatibilities of S1864/S1890).

6.  S1864 (a) is closed for every cospan of actual cover maps:
    S1945SitePseudofunctorCoherence proves S1890PseudofunctorCoherence for the
    constructed data; S1935RemainingSitePseudofunctor_holds proves the exact
    remaining obligation of S1935; S1864PartA is the corresponding (a)-form
    statement.  The remaining parts of S1864 are (b) IsStack, (c) the representably
    finite-etale structure map and (d) the universal property; none is claimed
    here.

## Honest boundary

No sorry, no axiom, no new assumption, no fake coherence.  Every comparison and
every coherence equation is an actual theorem about the actual S1726 covers; the
only axioms used are propext, Classical.choice and Quot.sound (see the
#print axioms block at the end).
-/
import tmp.sheaf.xif.paper.S1935CatCoherenceActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual

open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual

universe u

theorem siteCompGHom {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)
    (y : ↥(B.source.fiber.obj U)) :
    (g.map.app W).toFunctor.map ((B.source.fiber.mapComp φ ψ).hom.toNatTrans.app y) ≫
        (g.map.naturality ψ).hom.toNatTrans.app ((B.source.fiber.map φ).toFunctor.obj y) ≫
          (C.source.fiber.map ψ).toFunctor.map ((g.map.naturality φ).hom.toNatTrans.app y) =
      (g.map.naturality (φ ≫ ψ)).hom.toNatTrans.app y ≫
        (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app ((g.map.app U).toFunctor.obj y) :=
  (natCompHomApp_comp (F := B.source.fiber) (G := C.source.fiber) g.map φ ψ y).symm

section Comp

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteCompSquareAux (x : ↥(A.source.fiber.obj U)) (y : ↥(B.source.fiber.obj U))
    (h : (f.map.app U).toFunctor.obj x ⟶ (g.map.app U).toFunctor.obj y) :
    (f.map.app W).toFunctor.map ((A.source.fiber.mapComp φ ψ).hom.toNatTrans.app x) ≫
        (f.map.naturality ψ).hom.toNatTrans.app ((A.source.fiber.map φ).toFunctor.obj x) ≫
          (C.source.fiber.map ψ).toFunctor.map ((f.map.naturality φ).hom.toNatTrans.app x) ≫
            (C.source.fiber.map ψ).toFunctor.map ((C.source.fiber.map φ).toFunctor.map h) ≫
              (C.source.fiber.map ψ).toFunctor.map
                ((g.map.naturality φ).inv.toNatTrans.app y) ≫
                (g.map.naturality ψ).inv.toNatTrans.app
                  ((B.source.fiber.map φ).toFunctor.obj y)
      = (f.map.naturality (φ ≫ ψ)).hom.toNatTrans.app x ≫
          (C.source.fiber.map (φ ≫ ψ)).toFunctor.map h ≫
            (g.map.naturality (φ ≫ ψ)).inv.toNatTrans.app y ≫
              (g.map.app W).toFunctor.map
                ((B.source.fiber.mapComp φ ψ).hom.toNatTrans.app y) := by
  have hF := siteCompF (f := f) φ ψ x
  have hC := S1890SiteCompC (f := f) (g := g) φ ψ x y h
  have hG := siteCompG (g := g) φ ψ y
  let A1 := (f.map.app W).toFunctor.map ((A.source.fiber.mapComp φ ψ).hom.toNatTrans.app x)
  let A2 := (f.map.naturality ψ).hom.toNatTrans.app ((A.source.fiber.map φ).toFunctor.obj x)
  let A3 := (C.source.fiber.map ψ).toFunctor.map ((f.map.naturality φ).hom.toNatTrans.app x)
  let B1 := (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app ((f.map.app U).toFunctor.obj x)
  let D1 := (C.source.fiber.map ψ).toFunctor.map ((C.source.fiber.map φ).toFunctor.map h)
  let E1 := (C.source.fiber.map ψ).toFunctor.map ((g.map.naturality φ).inv.toNatTrans.app y)
  let F1 := (g.map.naturality ψ).inv.toNatTrans.app ((B.source.fiber.map φ).toFunctor.obj y)
  let R1 := (f.map.naturality (φ ≫ ψ)).hom.toNatTrans.app x
  let R2 := (C.source.fiber.map (φ ≫ ψ)).toFunctor.map h
  let B3 := (C.source.fiber.mapComp φ ψ).hom.toNatTrans.app ((g.map.app U).toFunctor.obj y)
  let R3 := (g.map.naturality (φ ≫ ψ)).inv.toNatTrans.app y
  let R4 := (g.map.app W).toFunctor.map ((B.source.fiber.mapComp φ ψ).hom.toNatTrans.app y)
  have hF' : A1 ≫ (A2 ≫ A3) = R1 ≫ B1 := hF
  have hC' : B1 ≫ D1 = R2 ≫ B3 := hC
  have hG' : B3 ≫ (E1 ≫ F1) = R3 ≫ R4 := hG
  calc
    A1 ≫ (A2 ≫ (A3 ≫ (D1 ≫ (E1 ≫ F1))))
        = (A1 ≫ (A2 ≫ A3)) ≫ (D1 ≫ (E1 ≫ F1)) := by simp only [Category.assoc]
    _ = (R1 ≫ B1) ≫ (D1 ≫ (E1 ≫ F1)) := by rw [hF']
    _ = R1 ≫ ((B1 ≫ D1) ≫ (E1 ≫ F1)) := by simp only [Category.assoc]
    _ = R1 ≫ ((R2 ≫ B3) ≫ (E1 ≫ F1)) := by rw [hC']
    _ = R1 ≫ (R2 ≫ (B3 ≫ (E1 ≫ F1))) := by simp only [Category.assoc]
    _ = R1 ≫ (R2 ≫ (R3 ≫ R4)) := by rw [hG']

theorem siteCompSquare :
    S1890CompSquare
      (ca := Cat.Hom.toNatIso (A.source.fiber.mapComp φ ψ))
      (cb := Cat.Hom.toNatIso (B.source.fiber.mapComp φ ψ))
      (a₁ := (A.source.fiber.map φ).toFunctor)
      (a₂ := (A.source.fiber.map ψ).toFunctor)
      (a₁₂ := (A.source.fiber.map (φ ≫ ψ)).toFunctor)
      (b₁ := (B.source.fiber.map φ).toFunctor)
      (b₂ := (B.source.fiber.map ψ).toFunctor)
      (b₁₂ := (B.source.fiber.map (φ ≫ ψ)).toFunctor)
      (c₁ := (C.source.fiber.map φ).toFunctor)
      (c₂ := (C.source.fiber.map ψ).toFunctor)
      (c₁₂ := (C.source.fiber.map (φ ≫ ψ)).toFunctor)
      (L₀ := (f.map.app U).toFunctor) (R₀ := (g.map.app U).toFunctor)
      (L₁ := (f.map.app V).toFunctor) (R₁ := (g.map.app V).toFunctor)
      (L₂ := (f.map.app W).toFunctor) (R₂ := (g.map.app W).toFunctor)
      (α₁ := S1864SiteComparisonLeft f φ)
      (β₁ := S1864SiteComparisonRight g φ)
      (α₂ := S1864SiteComparisonLeft f ψ)
      (β₂ := S1864SiteComparisonRight g ψ)
      (α₁₂ := S1864SiteComparisonLeft f (φ ≫ ψ))
      (β₁₂ := S1864SiteComparisonRight g (φ ≫ ψ)) := by
  intro x y h
  exact siteCompSquareAux f g φ ψ x y h

noncomputable def siteMapComp :
    S1890IsoCommaMap f g (φ ≫ ψ) ≅
      S1890IsoCommaMap f g φ ≫ S1890IsoCommaMap f g ψ :=
  Cat.Hom.isoMk (S1890RestrictCompIso (siteCompSquare f g φ ψ))

end Comp

section Id

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}

theorem siteIdC (x : ↥(A.source.fiber.obj U)) (y : ↥(B.source.fiber.obj U))
    (h : (f.map.app U).toFunctor.obj x ⟶ (g.map.app U).toFunctor.obj y) :
    (C.source.fiber.mapId U).hom.toNatTrans.app ((f.map.app U).toFunctor.obj x) ≫ h =
      (C.source.fiber.map (𝟙 U)).toFunctor.map h ≫
        (C.source.fiber.mapId U).hom.toNatTrans.app ((g.map.app U).toFunctor.obj y) :=
  (NatTrans.naturality (Cat.Hom.toNatIso (C.source.fiber.mapId U)).hom h).symm

theorem siteIdSquareAux (x : ↥(A.source.fiber.obj U)) (y : ↥(B.source.fiber.obj U))
    (h : (f.map.app U).toFunctor.obj x ⟶ (g.map.app U).toFunctor.obj y) :
    (f.map.app U).toFunctor.map ((A.source.fiber.mapId U).hom.toNatTrans.app x) ≫ h =
      ((f.map.naturality (𝟙 U)).hom.toNatTrans.app x ≫
          (C.source.fiber.map (𝟙 U)).toFunctor.map h ≫
            (g.map.naturality (𝟙 U)).inv.toNatTrans.app y) ≫
        (g.map.app U).toFunctor.map ((B.source.fiber.mapId U).hom.toNatTrans.app y) := by
  have hF := siteIdF (f := f) U x
  have hC := siteIdC (f := f) (g := g) x y h
  have hG := siteIdG (f := f) (g := g) (U := U) x y h
  let A1 := (f.map.app U).toFunctor.map ((A.source.fiber.mapId U).hom.toNatTrans.app x)
  let A2 := (f.map.naturality (𝟙 U)).hom.toNatTrans.app x
  let C1 := (C.source.fiber.mapId U).hom.toNatTrans.app ((f.map.app U).toFunctor.obj x)
  let B1 := (C.source.fiber.map (𝟙 U)).toFunctor.map h
  let C2 := (C.source.fiber.mapId U).hom.toNatTrans.app ((g.map.app U).toFunctor.obj y)
  let E1 := (g.map.naturality (𝟙 U)).inv.toNatTrans.app y
  let R4 := (g.map.app U).toFunctor.map ((B.source.fiber.mapId U).hom.toNatTrans.app y)
  have hF' : A1 = A2 ≫ C1 := hF
  have hC' : C1 ≫ h = B1 ≫ C2 := hC
  have hG' : E1 ≫ R4 = C2 := hG
  calc
    A1 ≫ h = (A2 ≫ C1) ≫ h := by rw [hF']
    _ = A2 ≫ (C1 ≫ h) := by simp only [Category.assoc]
    _ = A2 ≫ (B1 ≫ C2) := by rw [hC']
    _ = A2 ≫ (B1 ≫ (E1 ≫ R4)) := by rw [← hG']
    _ = (A2 ≫ (B1 ≫ E1)) ≫ R4 := by simp only [Category.assoc]

theorem siteIdSquare :
    S1890IdSquare
      (ca₀ := Cat.Hom.toNatIso (A.source.fiber.mapId U))
      (cb₀ := Cat.Hom.toNatIso (B.source.fiber.mapId U))
      (L := (f.map.app U).toFunctor) (R := (g.map.app U).toFunctor)
      (α₀ := S1864SiteComparisonLeft f (𝟙 U))
      (β₀ := S1864SiteComparisonRight g (𝟙 U))
      (c₀ := (C.source.fiber.map (𝟙 U)).toFunctor) := by
  intro x y h
  exact siteIdSquareAux f g x y h

noncomputable def siteMapId :
    S1890IsoCommaMap f g (𝟙 U) ≅ 𝟙 (S1890IsoCommaObj f g U) :=
  Cat.Hom.isoMk (S1890RestrictIdIso (siteIdSquare f g))

end Id

section Proj

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

theorem siteMapComp_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        ((siteMapComp f g φ ψ).hom.toNatTrans.app X) =
      (A.source.fiber.mapComp φ ψ).hom.toNatTrans.app X.obj.left := rfl

theorem siteMapComp_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        ((siteMapComp f g φ ψ).hom.toNatTrans.app X) =
      (B.source.fiber.mapComp φ ψ).hom.toNatTrans.app X.obj.right := rfl

theorem siteMapComp_inv_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        ((siteMapComp f g φ ψ).inv.toNatTrans.app X) =
      (A.source.fiber.mapComp φ ψ).inv.toNatTrans.app X.obj.left := rfl

theorem siteMapComp_inv_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        ((siteMapComp f g φ ψ).inv.toNatTrans.app X) =
      (B.source.fiber.mapComp φ ψ).inv.toNatTrans.app X.obj.right := rfl

theorem isoCommaMap_fst_map {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    {X Y : ↥(S1890IsoCommaObj f g U)} (m : X ⟶ Y) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map m) =
      (A.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map m) := rfl

theorem isoCommaMap_snd_map {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)
    {X Y : ↥(S1890IsoCommaObj f g U)} (m : X ⟶ Y) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((S1890IsoCommaMap f g φ).toFunctor.map m) =
      (B.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map m) := rfl

theorem obj_left_isoCommaMap (X : ↥(S1890IsoCommaObj f g U)) :
    ((S1890IsoCommaMap f g φ).toFunctor.obj X).obj.left =
      (A.source.fiber.map φ).toFunctor.obj X.obj.left := rfl

theorem obj_right_isoCommaMap (X : ↥(S1890IsoCommaObj f g U)) :
    ((S1890IsoCommaMap f g φ).toFunctor.obj X).obj.right =
      (B.source.fiber.map φ).toFunctor.obj X.obj.right := rfl

end Proj

section ProjId

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}

theorem siteMapId_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((siteMapId f g).hom.toNatTrans.app X) =
      (A.source.fiber.mapId U).hom.toNatTrans.app X.obj.left := rfl

theorem siteMapId_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((siteMapId f g).hom.toNatTrans.app X) =
      (B.source.fiber.mapId U).hom.toNatTrans.app X.obj.right := rfl

theorem siteMapId_inv_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((siteMapId f g).inv.toNatTrans.app X) =
      (A.source.fiber.mapId U).inv.toNatTrans.app X.obj.left := rfl

theorem siteMapId_inv_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map
        ((siteMapId f g).inv.toNatTrans.app X) =
      (B.source.fiber.mapId U).inv.toNatTrans.app X.obj.right := rfl

end ProjId

section Coh

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U V W Z : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
  (φ : U ⟶ V) (ψ : V ⟶ W) (χ : W ⟶ Z)


theorem source_map₂_assoc_app (X : ↥(S1890IsoCommaObj f g U)) :
    (A.source.fiber.map₂ (α_ φ ψ χ).hom).toNatTrans.app X.obj.left =
      eqToHom (by simp) := by
  rw [Bicategory.Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.eqToHom_app]

theorem coord_assoc (X : ↥(S1890IsoCommaObj f g U)) :
    (A.source.fiber.map₂ (α_ φ ψ χ).hom).toNatTrans.app X.obj.left =
      (A.source.fiber.mapComp (φ ≫ ψ) χ).hom.toNatTrans.app X.obj.left ≫
        (A.source.fiber.map χ).toFunctor.map
          ((A.source.fiber.mapComp φ ψ).hom.toNatTrans.app X.obj.left) ≫
          (α_ (A.source.fiber.map φ) (A.source.fiber.map ψ) (A.source.fiber.map χ)).hom.toNatTrans.app
            X.obj.left ≫
            (A.source.fiber.mapComp ψ χ).inv.toNatTrans.app
              ((A.source.fiber.map φ).toFunctor.obj X.obj.left) ≫
              (A.source.fiber.mapComp φ (ψ ≫ χ)).inv.toNatTrans.app X.obj.left := by
  have h := congrArg (fun η => η.toNatTrans.app X.obj.left)
    (A.source.fiber.map₂_associator φ ψ χ)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app] using h


theorem coord_assoc_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (B.source.fiber.map₂ (α_ φ ψ χ).hom).toNatTrans.app X.obj.right =
      (B.source.fiber.mapComp (φ ≫ ψ) χ).hom.toNatTrans.app X.obj.right ≫
        (B.source.fiber.map χ).toFunctor.map
          ((B.source.fiber.mapComp φ ψ).hom.toNatTrans.app X.obj.right) ≫
          (α_ (B.source.fiber.map φ) (B.source.fiber.map ψ) (B.source.fiber.map χ)).hom.toNatTrans.app
            X.obj.right ≫
            (B.source.fiber.mapComp ψ χ).inv.toNatTrans.app
              ((B.source.fiber.map φ).toFunctor.obj X.obj.right) ≫
              (B.source.fiber.mapComp φ (ψ ≫ χ)).inv.toNatTrans.app X.obj.right := by
  have h := congrArg (fun η => η.toNatTrans.app X.obj.right)
    (B.source.fiber.map₂_associator φ ψ χ)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app] using h

theorem source_map₂_assoc_snd_app (X : ↥(S1890IsoCommaObj f g U)) :
    (B.source.fiber.map₂ (α_ φ ψ χ).hom).toNatTrans.app X.obj.right =
      eqToHom (by simp) := by
  rw [Bicategory.Strict.associator_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.eqToHom_app]


theorem siteAssociator_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app Z).toFunctor (g.map.app Z).toFunctor).map
        ((α_ (S1890IsoCommaMap f g φ) (S1890IsoCommaMap f g ψ)
          (S1890IsoCommaMap f g χ)).hom.toNatTrans.app X) =
      (α_ (A.source.fiber.map φ) (A.source.fiber.map ψ)
        (A.source.fiber.map χ)).hom.toNatTrans.app X.obj.left := rfl

theorem siteAssociator_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app Z).toFunctor (g.map.app Z).toFunctor).map
        ((α_ (S1890IsoCommaMap f g φ) (S1890IsoCommaMap f g ψ)
          (S1890IsoCommaMap f g χ)).hom.toNatTrans.app X) =
      (α_ (B.source.fiber.map φ) (B.source.fiber.map ψ)
        (B.source.fiber.map χ)).hom.toNatTrans.app X.obj.right := rfl

theorem siteCoherence_assoc :
    (siteMapComp f g (φ ≫ ψ) χ).hom ≫
        (siteMapComp f g φ ψ).hom ▷ S1890IsoCommaMap f g χ ≫
          (α_ (S1890IsoCommaMap f g φ) (S1890IsoCommaMap f g ψ)
            (S1890IsoCommaMap f g χ)).hom ≫
            S1890IsoCommaMap f g φ ◁ (siteMapComp f g ψ χ).inv ≫
              (siteMapComp f g φ (ψ ≫ χ)).inv = eqToHom (by simp) := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply S1836IsoComma_hom_ext (f.map.app Z).toFunctor (g.map.app Z).toFunctor
  · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      siteAssociator_fst, Cat.eqToHom_app, CategoryTheory.eqToHom_map,
      siteMapComp_fst, siteMapComp_inv_fst,
      isoCommaMap_fst_map, obj_left_isoCommaMap, Functor.map_comp,
      Category.comp_id, Category.id_comp, Category.assoc]
    exact (coord_assoc f g φ ψ χ X).symm.trans (source_map₂_assoc_app f g φ ψ χ X)
  · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      siteAssociator_snd, Cat.eqToHom_app, CategoryTheory.eqToHom_map,
      siteMapComp_snd, siteMapComp_inv_snd,
      isoCommaMap_snd_map, obj_right_isoCommaMap, Functor.map_comp,
      Category.comp_id, Category.id_comp, Category.assoc]
    exact (coord_assoc_snd f g φ ψ χ X).symm.trans (source_map₂_assoc_snd_app f g φ ψ χ X)

end Coh


section Unit

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V)

theorem siteLeftUnitor_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((λ_ (S1890IsoCommaMap f g φ)).hom.toNatTrans.app X) =
      (λ_ (A.source.fiber.map φ)).hom.toNatTrans.app X.obj.left := rfl

theorem siteLeftUnitor_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((λ_ (S1890IsoCommaMap f g φ)).hom.toNatTrans.app X) =
      (λ_ (B.source.fiber.map φ)).hom.toNatTrans.app X.obj.right := rfl

theorem siteRightUnitor_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((ρ_ (S1890IsoCommaMap f g φ)).hom.toNatTrans.app X) =
      (ρ_ (A.source.fiber.map φ)).hom.toNatTrans.app X.obj.left := rfl

theorem siteRightUnitor_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        ((ρ_ (S1890IsoCommaMap f g φ)).hom.toNatTrans.app X) =
      (ρ_ (B.source.fiber.map φ)).hom.toNatTrans.app X.obj.right := rfl

theorem source_map₂_leftUnitor_app (X : ↥(S1890IsoCommaObj f g U)) :
    (A.source.fiber.map₂ (λ_ φ).hom).toNatTrans.app X.obj.left = eqToHom (by simp) := by
  rw [Bicategory.Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.eqToHom_app]

theorem source_map₂_leftUnitor_snd_app (X : ↥(S1890IsoCommaObj f g U)) :
    (B.source.fiber.map₂ (λ_ φ).hom).toNatTrans.app X.obj.right = eqToHom (by simp) := by
  rw [Bicategory.Strict.leftUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.eqToHom_app]

theorem source_map₂_rightUnitor_app (X : ↥(S1890IsoCommaObj f g U)) :
    (A.source.fiber.map₂ (ρ_ φ).hom).toNatTrans.app X.obj.left = eqToHom (by simp) := by
  rw [Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.eqToHom_app]

theorem source_map₂_rightUnitor_snd_app (X : ↥(S1890IsoCommaObj f g U)) :
    (B.source.fiber.map₂ (ρ_ φ).hom).toNatTrans.app X.obj.right = eqToHom (by simp) := by
  rw [Bicategory.Strict.rightUnitor_eqToIso, eqToIso.hom, PrelaxFunctor.map₂_eqToHom]
  simp only [Cat.eqToHom_app]

theorem coord_leftUnitor_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (A.source.fiber.map₂ (λ_ φ).hom).toNatTrans.app X.obj.left =
      (A.source.fiber.mapComp (𝟙 U) φ).hom.toNatTrans.app X.obj.left ≫
        (A.source.fiber.map φ).toFunctor.map
          ((A.source.fiber.mapId U).hom.toNatTrans.app X.obj.left) ≫
          (λ_ (A.source.fiber.map φ)).hom.toNatTrans.app X.obj.left := by
  have h := congrArg (fun η => η.toNatTrans.app X.obj.left)
    (A.source.fiber.map₂_left_unitor φ)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app] using h

theorem coord_leftUnitor_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (B.source.fiber.map₂ (λ_ φ).hom).toNatTrans.app X.obj.right =
      (B.source.fiber.mapComp (𝟙 U) φ).hom.toNatTrans.app X.obj.right ≫
        (B.source.fiber.map φ).toFunctor.map
          ((B.source.fiber.mapId U).hom.toNatTrans.app X.obj.right) ≫
          (λ_ (B.source.fiber.map φ)).hom.toNatTrans.app X.obj.right := by
  have h := congrArg (fun η => η.toNatTrans.app X.obj.right)
    (B.source.fiber.map₂_left_unitor φ)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerRight_app] using h

theorem coord_rightUnitor_fst (X : ↥(S1890IsoCommaObj f g U)) :
    (A.source.fiber.map₂ (ρ_ φ).hom).toNatTrans.app X.obj.left =
      (A.source.fiber.mapComp φ (𝟙 V)).hom.toNatTrans.app X.obj.left ≫
        (A.source.fiber.mapId V).hom.toNatTrans.app
          ((A.source.fiber.map φ).toFunctor.obj X.obj.left) ≫
          (ρ_ (A.source.fiber.map φ)).hom.toNatTrans.app X.obj.left := by
  have h := congrArg (fun η => η.toNatTrans.app X.obj.left)
    (A.source.fiber.map₂_right_unitor φ)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app] using h

theorem coord_rightUnitor_snd (X : ↥(S1890IsoCommaObj f g U)) :
    (B.source.fiber.map₂ (ρ_ φ).hom).toNatTrans.app X.obj.right =
      (B.source.fiber.mapComp φ (𝟙 V)).hom.toNatTrans.app X.obj.right ≫
        (B.source.fiber.mapId V).hom.toNatTrans.app
          ((B.source.fiber.map φ).toFunctor.obj X.obj.right) ≫
          (ρ_ (B.source.fiber.map φ)).hom.toNatTrans.app X.obj.right := by
  have h := congrArg (fun η => η.toNatTrans.app X.obj.right)
    (B.source.fiber.map₂_right_unitor φ)
  simpa only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app] using h

theorem siteCoherence_leftUnitor :
    (siteMapComp f g (𝟙 U) φ).hom ≫
        (siteMapId f g).hom ▷ S1890IsoCommaMap f g φ ≫
          (λ_ (S1890IsoCommaMap f g φ)).hom = eqToHom (by simp) := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply S1836IsoComma_hom_ext (f.map.app V).toFunctor (g.map.app V).toFunctor
  · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      siteLeftUnitor_fst, Cat.eqToHom_app, CategoryTheory.eqToHom_map,
      siteMapComp_fst, siteMapId_fst, isoCommaMap_fst_map, obj_left_isoCommaMap,
      Functor.map_comp, Category.comp_id]
    exact (coord_leftUnitor_fst f g φ X).symm.trans (source_map₂_leftUnitor_app f g φ X)
  · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      siteLeftUnitor_snd, Cat.eqToHom_app, CategoryTheory.eqToHom_map,
      siteMapComp_snd, siteMapId_snd, isoCommaMap_snd_map, obj_right_isoCommaMap,
      Functor.map_comp, Category.comp_id]
    exact (coord_leftUnitor_snd f g φ X).symm.trans (source_map₂_leftUnitor_snd_app f g φ X)

theorem siteCoherence_rightUnitor :
    (siteMapComp f g φ (𝟙 V)).hom ≫
        S1890IsoCommaMap f g φ ◁ (siteMapId f g).hom ≫
          (ρ_ (S1890IsoCommaMap f g φ)).hom = eqToHom (by simp) := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply S1836IsoComma_hom_ext (f.map.app V).toFunctor (g.map.app V).toFunctor
  · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      siteRightUnitor_fst, Cat.eqToHom_app, CategoryTheory.eqToHom_map,
      siteMapComp_fst, siteMapId_fst, isoCommaMap_fst_map, obj_left_isoCommaMap,
      Functor.map_comp, Category.comp_id]
    exact (coord_rightUnitor_fst f g φ X).symm.trans (source_map₂_rightUnitor_app f g φ X)
  · simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
      siteRightUnitor_snd, Cat.eqToHom_app, CategoryTheory.eqToHom_map,
      siteMapComp_snd, siteMapId_snd, isoCommaMap_snd_map, obj_right_isoCommaMap,
      Functor.map_comp, Category.comp_id]
    exact (coord_rightUnitor_snd f g φ X).symm.trans (source_map₂_rightUnitor_snd_app f g φ X)

end Unit


section Assemble

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- **The iso-comma site pseudofunctor**, constructed from the restriction comparisons
of S1890 and the three coherence laws proved in this file. -/
noncomputable def sitePseudofunctor :
    LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ ⥤ᵖ Cat :=
  pseudofunctorOfIsLocallyDiscrete (fun U => S1890IsoCommaObj f g U)
    (fun {U V} (φ : U ⟶ V) => S1890IsoCommaMap f g φ)
    (fun U => siteMapId f g)
    (fun {U V W} (φ : U ⟶ V) (ψ : V ⟶ W) => siteMapComp f g φ ψ)
    (fun {U V W Z} (φ : U ⟶ V) (ψ : V ⟶ W) (χ : W ⟶ Z) =>
      siteCoherence_assoc f g φ ψ χ)
    (fun {U V} (φ : U ⟶ V) => siteCoherence_leftUnitor f g φ)
    (fun {U V} (φ : U ⟶ V) => siteCoherence_rightUnitor f g φ)

theorem sitePseudofunctor_obj (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (sitePseudofunctor f g).obj U = S1890IsoCommaObj f g U := rfl

theorem sitePseudofunctor_map {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) :
    (sitePseudofunctor f g).map φ = S1890IsoCommaMap f g φ := rfl

theorem sitePseudofunctor_mapComp {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) :
    (sitePseudofunctor f g).mapComp φ ψ = siteMapComp f g φ ψ := rfl

theorem sitePseudofunctor_mapId (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    (sitePseudofunctor f g).mapId U = siteMapId f g := rfl

/-- **The pseudofunctor coherence for the constructed site comparison data.** -/
theorem S1945SitePseudofunctorCoherence :
    S1890PseudofunctorCoherence f g
      (fun {U V W} (φ : U ⟶ V) (ψ : V ⟶ W) => siteMapComp f g φ ψ)
      (fun U => siteMapId f g) :=
  ⟨fun φ ψ χ => siteCoherence_assoc f g φ ψ χ,
   fun φ => siteCoherence_leftUnitor f g φ,
   fun φ => siteCoherence_rightUnitor f g φ⟩

/-- **S1864 (a) closed**: the exact remaining site-pseudofunctor obligation of S1935
is now inhabited by the data built from `S1890RestrictCompIso` and
`S1890RestrictIdIso`, with the three coherence laws proved (not assumed). -/
theorem S1935RemainingSitePseudofunctor_holds :
    S1935RemainingSitePseudofunctor f g :=
  ⟨fun {U V W} (φ : U ⟶ V) (ψ : V ⟶ W) => siteMapComp f g φ ψ,
   fun U => siteMapId f g,
   S1945SitePseudofunctorCoherence f g⟩

end Assemble

/-! ## 8. S1864 (a) in the exact shape of the missing statement -/

/-- **S1864 (a)**, with the canonical witness: the iso-comma site pseudofunctor
built here has the required values (the iso-comma categories of the two
cover-map fibres) and the required 1-cells (the site restrictions of S1864/S1890),
both definitionally.  This is the (a) part of S1864's missing statement;
(b) IsStack, (c) the finite-etale structure map and (d) the universal property are
not addressed here. -/
theorem S1864PartA {A B C : S1728Cover} (f : S1728CoverMap A C)
    (g : S1728CoverMap B C) :
    (∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
        (sitePseudofunctor f g).obj U = S1890IsoCommaObj f g U) ∧
      (∀ {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V),
        (sitePseudofunctor f g).map φ = S1890IsoCommaMap f g φ) :=
  ⟨fun U => rfl, fun φ => rfl⟩

/-! ## 9. Checks and axiom audit -/

#check siteCompGHom
#check siteCompSquare
#check siteIdSquare
#check siteMapComp
#check siteMapId
#check siteCoherence_assoc
#check siteCoherence_leftUnitor
#check siteCoherence_rightUnitor
#check sitePseudofunctor
#check sitePseudofunctor_obj
#check sitePseudofunctor_map
#check sitePseudofunctor_mapComp
#check sitePseudofunctor_mapId
#check S1945SitePseudofunctorCoherence
#check S1935RemainingSitePseudofunctor_holds
#check S1864PartA

#print axioms siteCompGHom
#print axioms siteCompSquare
#print axioms siteIdSquare
#print axioms siteMapComp
#print axioms siteMapId
#print axioms siteCoherence_assoc
#print axioms siteCoherence_leftUnitor
#print axioms siteCoherence_rightUnitor
#print axioms sitePseudofunctor
#print axioms S1945SitePseudofunctorCoherence
#print axioms S1935RemainingSitePseudofunctor_holds
#print axioms S1864PartA

end LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
