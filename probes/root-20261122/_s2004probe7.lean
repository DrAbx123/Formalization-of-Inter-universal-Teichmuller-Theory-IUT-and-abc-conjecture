/-
# S2004: effectivity of the iso-comma stack -- the push-forward of descent data

## Context

S1998 proved the prestack half `S1956IsoCommaPrestack f g` of the iso-comma site
pseudofunctor `sitePseudofunctor f g` of the two actual finite-etale cover maps
`f : A ⟶ C` and `g : B ⟶ C`.  The exact remaining half of the S1956/S1864 (b)
target is the effectivity statement

  `S1956IsoCommaEffectivity f g`
    = `∀ (S) (R : Sieve S), R ∈ J S →
         ((sitePseudofunctor f g).toDescentData (fun i => i.obj.hom)).EssSurj`,

i.e. the object-level essential surjectivity of the descent-data comparison for the
iso-comma pseudofunctor.  S1998 supplies the consumer
`S1956IsoCommaEffectivity f g → S1956IsoCommaStack f g`
(`S1998IsoCommaStack_of_effectivity`).

## What is proved in this file

The object-level effectivity is the 2-limit interchange: a descent datum for the
iso-comma pseudofunctor has to be split into descent data for the three stacks and
a comparison.  The first, and technically hardest, piece of that interchange is
the functoriality of the `f`- and `g`-side components: a **strong transformation
of pseudofunctors sends descent data to descent data**.  This file proves it:

1.  `S2004Push_coherence`: the two-legged componentwise coherence which says that
    the H-comparison components (the naturality isomorphisms of a strong
    transformation `α : F ⟶ G`) are compatible with two *different* restriction
    legs.  This is the two-legged generalization of `S1988HComponent_pullHom`
    (S1988 is the one-legged case); the proof is the same associativity and
    cancellation computation, assembled from the two S1935 component coherences
    (`natCompInvApp_comp_mapComp'`, `natCompHomApp_comp_mapComp'`) and the
    naturality of the comparison itself.

2.  `S2004PushDescentData`: for every strong transformation `α : F ⟶ G` of
    pseudofunctors on the etale site and every descent datum `D` for `F` along the
    arrows of a sieve, the transported descent datum for `G`.  The three axioms
    `pullHom_hom`, `hom_self`, `hom_comp` are proved (from 1, and from the
    unit/cancellation laws of the comparison isomorphisms).

3.  `S2004MidF`, `S2004MidG`: its specializations to the `f`-side and the
    `g`-side of an iso-comma descent datum.

## Honest boundary: the exact first missing

The effectivity statement `S1956IsoCommaEffectivity f g` is **not** proved here.
Given a descent datum `D` of the iso-comma pseudofunctor, the remaining steps are

  (a) `S2004MidComparison` (the exact first missing): the family of middle
      isomorphisms `(D.obj i).obj.hom : (f-side i) ≅ (g-side i)` is a morphism of
      `C`-descent data `S2004MidF D ⟶ S2004MidG D`;
  (b) the comparison with `C.toDescentData`: for an effective `A`-descent datum
      `a` with `A.toDescentData a ≅ S2004FstDescentData D` (and similarly `b` on
      the `B`-side), the canonical candidate is an isomorphism of `C`-descent data
      `C.toDescentData ((f.map.app _).obj a) ≅ S2004MidF D`;
  (c) the reassembly: full faithfulness of `C.toDescentData` (the `C`-stack is a
      prestack) turns (a) + (b) into an isomorphism
      `(f.map.app _).obj a ≅ (g.map.app _).obj b`, and the resulting iso-comma
      object maps to `D` under `toDescentData`.

None of (a), (b), (c) is asserted here; they are named `Prop`s/`def`s without
inhabitants only where explicitly stated.  No `sorry`, no `axiom`, no `Shrink`,
`ULift` or `PUnit`, and no change of the target.  The only axioms used are
`propext`, `Classical.choice` and `Quot.sound`; see the `#print axioms` block.
-/
import tmp.sheaf.xif.paper.S1998IsoCommaPrestackActual


noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option pp.all false
set_option pp.proofs false
set_option backward.isDefEq.respectTransparency false

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

section Push

variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}
  {S : Site} {R : Sieve S}

/-- The family of arrows of a sieve. -/
abbrev Rfam (R : Sieve S) : R.arrows.category → Site := fun i => i.obj.left

/-- The image of a descent datum under a strong transformation. -/
noncomputable def S2004PushDescentData
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G)
    (D : F.DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    G.DescentData (fun (i : R.arrows.category) => i.obj.hom) where
  obj i := (α.app (U (Rfam R i))).toFunctor.obj (D.obj i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
      (α.app (U Y)).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
        (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)
  pullHom_hom Y' Y gg q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    have hD := D.pullHom_hom gg q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    have h := S2004Push_coherence α gg gf₁ gf₂ hgf₁ hgf₂ (D.hom q f₁ f₂ hf₁ hf₂)
    rw [hD] at h
    exact h.symm
  hom_self Y q i mm hmm := by
    have hD := D.hom_self q mm hmm
    have hc : (α.naturality mm.op.toLoc).inv.toNatTrans.app (D.obj i) ≫
        (α.naturality mm.op.toLoc).hom.toNatTrans.app (D.obj i) = 𝟙 _ := by
      rw [← Cat.Hom₂.comp_app, (α.naturality mm.op.toLoc).inv_hom_id, Cat.Hom₂.id_app]
    rw [hD]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.id_comp]
    exact hc
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have hD := D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃
    have hc : (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂) ≫
        (α.naturality f₂.op.toLoc).inv.toNatTrans.app (D.obj i₂) = 𝟙 _ := by
      rw [← Cat.Hom₂.comp_app, (α.naturality f₂.op.toLoc).hom_inv_id, Cat.Hom₂.id_app]
    calc ((α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          (α.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)) ≫
          ((α.naturality f₂.op.toLoc).inv.toNatTrans.app (D.obj i₂) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₂ f₃ hf₂ hf₃) ≫
          (α.naturality f₃.op.toLoc).hom.toNatTrans.app (D.obj i₃))
        = (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          ((α.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂) ≫
          (α.naturality f₂.op.toLoc).inv.toNatTrans.app (D.obj i₂)) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₂ f₃ hf₂ hf₃) ≫
          (α.naturality f₃.op.toLoc).hom.toNatTrans.app (D.obj i₃) := by
          simp only [Category.assoc]
      _ = (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₂ f₃ hf₂ hf₃) ≫
          (α.naturality f₃.op.toLoc).hom.toNatTrans.app (D.obj i₃) := by
          erw [hc]
          simp
      _ = (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          ((α.app (U Y)).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₂ f₃ hf₂ hf₃)) ≫
          (α.naturality f₃.op.toLoc).hom.toNatTrans.app (D.obj i₃) := by
          simp only [Category.assoc]
      _ = (α.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
          (α.app (U Y)).toFunctor.map (D.hom q f₁ f₃ hf₁ hf₃) ≫
          (α.naturality f₃.op.toLoc).hom.toNatTrans.app (D.obj i₃) := by
          erw [← Functor.map_comp, hD]

end Push

/-! ## 3. The A-side descent datum of an iso-comma descent datum -/

section Extract

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} {R : Sieve S}

/-- Projection of `pullHom` along the first iso-comma projection. -/
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

/-- The descent datum of the A-fibre underlying a descent datum of the iso-comma. -/
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
    rw [S2004Fst_pullHom_raw f g _ gg gf₁ gf₂ hgf₁ hgf₂] at h2
    exact h2
  hom_self Y q i mm hmm := by
    have hD := D.hom_self q mm hmm
    have h2 := congrArg (fun m =>
      (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map m) hD
    rw [h2]
    rfl
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have hD := D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃
    have h2 := congrArg (fun m =>
      (S1836IsoCommaFst (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map m) hD
    rw [← h2]
    exact ((S1836IsoCommaFst (f.map.app (U Y)).toFunctor
      (g.map.app (U Y)).toFunctor).map_comp _ _).symm

end Extract

/-! ## 4. The B-side descent data and the middle C-descent data -/

section Mid

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} {R : Sieve S}

/-- Projection of C-side `pullHom` along the second iso-comma projection. -/
theorem S2004Snd_pullHom_raw {X₁ X₂ Y Y' : Site}
    {M₁ : (sitePseudofunctor f g).obj (U X₁)} {M₂ : (sitePseudofunctor f g).obj (U X₂)}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (u : ((sitePseudofunctor f g).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
         ((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.obj M₂)
    (gg : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : gg ≫ f₁ = gf₁ := by cat_disch) (hgf₂ : gg ≫ f₂ = gf₂ := by cat_disch) :
    (S1836IsoCommaSnd (f.map.app (U Y')).toFunctor (g.map.app (U Y')).toFunctor).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := sitePseudofunctor f g) u gg gf₁ gf₂
          hgf₁ hgf₂) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := B.source.fiber)
        ((S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map u)
        gg gf₁ gf₂ hgf₁ hgf₂ := by
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  simp only [Functor.map_comp, Category.assoc]
  rw [S1956Snd_mapComp', S1956Snd_map, S1956Snd_mapComp'_inv]

/-- The descent datum of the B-fibre underlying a descent datum of the iso-comma. -/
noncomputable def S2004SndDescentData
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    B.source.fiber.DescentData (fun (i : R.arrows.category) => i.obj.hom) where
  obj i := (D.obj i).obj.right
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map
      (D.hom q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' Y gg q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    have hD := D.pullHom_hom gg q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    have h2 := congrArg (fun m =>
      (S1836IsoCommaSnd (f.map.app (U Y')).toFunctor (g.map.app (U Y')).toFunctor).map m) hD
    rw [S2004Snd_pullHom_raw f g _ gg gf₁ gf₂ hgf₁ hgf₂] at h2
    exact h2
  hom_self Y q i mm hmm := by
    have hD := D.hom_self q mm hmm
    have h2 := congrArg (fun m =>
      (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map m) hD
    rw [h2]
    rfl
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have hD := D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃
    have h2 := congrArg (fun m =>
      (S1836IsoCommaSnd (f.map.app (U Y)).toFunctor (g.map.app (U Y)).toFunctor).map m) hD
    rw [← h2]
    exact ((S1836IsoCommaSnd (f.map.app (U Y)).toFunctor
      (g.map.app (U Y)).toFunctor).map_comp _ _).symm

/-- The `f`-side `C`-descent datum of an iso-comma descent datum. -/
noncomputable def S2004MidF
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    C.source.fiber.DescentData (fun (i : R.arrows.category) => i.obj.hom) :=
  S2004PushDescentData f.map (S2004FstDescentData f g D)

/-- The `g`-side `C`-descent datum of an iso-comma descent datum. -/
noncomputable def S2004MidG
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    C.source.fiber.DescentData (fun (i : R.arrows.category) => i.obj.hom) :=
  S2004PushDescentData g.map (S2004SndDescentData f g D)


/-- The middle comparison: the comma structure isomorphisms of an iso-comma descent datum
form a morphism of `C`-descent data between the `f`-side and the `g`-side push-forwards. -/
noncomputable def S2004MidComparison
    (D : (sitePseudofunctor f g).DescentData (fun (i : R.arrows.category) => i.obj.hom)) :
    S2004MidF f g D ≅ S2004MidG f g D :=
  Pseudofunctor.DescentData.isoMk (fun i => by
    haveI : IsIso (D.obj i).obj.hom := (D.obj i).2
    exact asIso (D.obj i).obj.hom) (by
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    simp only [S2004MidF, S2004MidG, S2004PushDescentData, S2004FstDescentData,
      S2004SndDescentData, S1864SiteComparisonLeft, S1864SiteComparisonRight, asIso_hom]
    have hw := (D.hom q f₁ f₂ hf₁ hf₂).hom.w
    have h1 : (((sitePseudofunctor f g).map f₁.op.toLoc).toFunctor.obj (D.obj i₁)).obj.hom =
        (S1864SiteComparisonLeft f f₁.op.toLoc).hom.app ((D.obj i₁).obj.left) ≫
          (C.source.fiber.map f₁.op.toLoc).toFunctor.map ((D.obj i₁).obj.hom) ≫
          (S1864SiteComparisonRight g f₁.op.toLoc).hom.app ((D.obj i₁).obj.right) :=
      S1998ObjHom f g (D.obj i₁) (Opposite.op (Over.mk f₁))
    have h2 : (((sitePseudofunctor f g).map f₂.op.toLoc).toFunctor.obj (D.obj i₂)).obj.hom =
        (S1864SiteComparisonLeft f f₂.op.toLoc).hom.app ((D.obj i₂).obj.left) ≫
          (C.source.fiber.map f₂.op.toLoc).toFunctor.map ((D.obj i₂).obj.hom) ≫
          (S1864SiteComparisonRight g f₂.op.toLoc).hom.app ((D.obj i₂).obj.right) :=
      S1998ObjHom f g (D.obj i₂) (Opposite.op (Over.mk f₂))
    rw [h1, h2] at hw
    simp only [S1864SiteComparisonLeft, S1864SiteComparisonRight, Cat.Hom.toNatIso,
      Iso.symm_hom] at hw
    have e1 : (f.map.naturality f₁.op.toLoc).inv.toNatTrans.app ((D.obj i₁).obj.left) ≫
        (f.map.naturality f₁.op.toLoc).hom.toNatTrans.app ((D.obj i₁).obj.left) = 𝟙 _ := by
      rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
    have e2 : (g.map.naturality f₂.op.toLoc).inv.toNatTrans.app ((D.obj i₂).obj.right) ≫
        (g.map.naturality f₂.op.toLoc).hom.toNatTrans.app ((D.obj i₂).obj.right) = 𝟙 _ := by
      rw [← Cat.Hom₂.comp_app, Iso.inv_hom_id, Cat.Hom₂.id_app]
    have hw' := congrArg (fun m =>
      (f.map.naturality f₁.op.toLoc).inv.toNatTrans.app ((D.obj i₁).obj.left) ≫
        m ≫ (g.map.naturality f₂.op.toLoc).hom.toNatTrans.app ((D.obj i₂).obj.right)) hw
    simp only [Category.assoc] at hw'
    simp only [← Category.assoc, e1, Category.id_comp] at hw'
    simp only [Category.assoc] at hw'
    simp only [e2, Category.id_comp] at hw'
    simp at hw'
    simpa only [S1836IsoCommaFst, S1836IsoCommaSnd, Functor.comp_map, ObjectProperty.ι_map,
      Comma.fst, Comma.snd, Category.assoc] using hw'.symm)

end Mid

end LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual