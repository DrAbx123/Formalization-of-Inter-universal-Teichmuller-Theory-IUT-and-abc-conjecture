import tmp.sheaf.xif.paper.S1970IsoCommaStackActual

/-!
# S1988: componentwise naturality of the H-comparison maps -- the S1970/S1956
first missing is closed

## Context

S1970 reduced the first missing statement for the prestack half of S1956/S1864 (b)
to

  (A) S1956HComparisonNaturalityAll = S1970HComparisonNaturalityAll

the componentwise naturality of the two H-comparison maps built from the strong
transformations `f.map` and `g.map` and the site comparisons
`S1864SiteComparisonLeft` / `S1864SiteComparisonRight`.  The previous attempt
identified the three correct ingredients already in the tree:

* `natCompInvApp_comp` (S1935) for the inverse comparison of `f.map` at the
  source,
* the naturality of the comparison at the middle site morphism (the
  `q`-comparison),
* `natCompHomApp_comp` (S1935) for the hom comparison of `f.map` at the target.

The missing formal work was the componentwise associativity/cancellation that
glues the three identities through the `pullHom` restriction maps and the
`Cat.Hom.toNatIso` comparisons.  This file completes exactly that assembly.

## What is proved

1.  Two generalized component identities
    `natCompInvApp_comp_mapComp'` and `natCompHomApp_comp_mapComp'`: the
    S1935 coherence identities restated for an arbitrary composite comparison
    `F.mapComp' f g fg h` (not only the definitional case `fg = f ≫ g`).
    They are obtained from S1935 by `cases h` and `mapComp'_eq_mapComp`.

2.  The generic core computation `S1988HComponent_naturality_core`: for an
    arbitrary strong transformation `α : F ⟶ G` of pseudofunctors
    `LocallyDiscrete Siteᵒᵖ ⤳ Cat`, the conjugation of a morphism by the
    naturality comparison of `α` is compatible with the restrictions along a
    composable pair of site morphisms.  The proof is the componentwise
    associativity/cancellation: the two coherence identities above give the
    outer square, naturality of the `q`-comparison gives the inner square, and
    the inverse comparisons are cancelled against the comparisons using
    `Cat.Hom₂.comp_app`.

3.  The generic component `S1988HComponent` and its naturality as a morphism
    of hom presheaves (`S1988HComponent_naturality`), for every strong
    transformation `α` and every pair of objects.

4.  The two concrete H-comparisons of S1956 are definitionally the generic
    component for `f.map` and `g.map` respectively
    (`S1956FstToHComponent_eq`, `S1956SndToHComponent_eq`).  Consequently the
    exact first missing (A) holds:

      `S1988HComparisonNaturalityAll : S1956HComparisonNaturalityAll`
      `S1988S1970HComparisonNaturalityAll : S1970HComparisonNaturalityAll`.

## The exact next missing

The prestack half is `S1956IsoCommaPrestack f g`.  Given the naturality (A),
the remaining step is the identification of the iso-comma hom presheaf with the
fibre product of the A-, B- and C-hom presheaves over the C-hom presheaf, and
the fact that a fibre product of sheaves is a sheaf.  This is *not* formalized
here and is not asserted.  The effectivity half `S1956IsoCommaEffectivity` is
the object-level 2-limit interchange and is likewise not addressed.

## Honest boundary

No `sorry`, no `axiom`, no `Shrink`, `ULift` or `PUnit`, and no change of
the target.  The only axioms used by the results of this file are `propext`,
`Classical.choice` and `Quot.sound`; see the `#print axioms` block.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1988HComparisonNaturalityActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1970IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1935CatCoherenceActual

universe v u

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

abbrev IsoCommaObjAt {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (S : Site) :=
  S1836IsoComma (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor

/-! ## 1. The component identities at an arbitrary composite comparison -/

/-- **Inverse-direction coherence at an arbitrary composite comparison.**
S1935's `natCompInvApp_comp` restated for `F.mapComp' f g fg h`. -/
theorem natCompInvApp_comp_mapComp' {B : Type u} [Bicategory B]
    {F G : Pseudofunctor B Cat.{v, v}} (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (x : ↑(F.obj a)) :
    (G.mapComp' f g fg h).hom.toNatTrans.app ((α.app a).toFunctor.obj x) ≫
        (G.map g).toFunctor.map ((α.naturality f).inv.toNatTrans.app x) ≫
          (α.naturality g).inv.toNatTrans.app ((F.map f).toFunctor.obj x) =
      (α.naturality fg).inv.toNatTrans.app x ≫
        (α.app c).toFunctor.map ((F.mapComp' f g fg h).hom.toNatTrans.app x) := by
  cases h
  simpa only [Pseudofunctor.mapComp'_eq_mapComp] using
    natCompInvApp_comp (F := F) (G := G) α f g x

/-- **Hom-direction coherence at an arbitrary composite comparison.**
S1935's `natCompHomApp_comp` restated for `F.mapComp' f g fg h`. -/
theorem natCompHomApp_comp_mapComp' {B : Type u} [Bicategory B]
    {F G : Pseudofunctor B Cat.{v, v}} (α : Pseudofunctor.StrongTrans F G)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (x : ↑(F.obj a)) :
    (α.naturality fg).hom.toNatTrans.app x ≫
        (G.mapComp' f g fg h).hom.toNatTrans.app ((α.app a).toFunctor.obj x) =
      (α.app c).toFunctor.map ((F.mapComp' f g fg h).hom.toNatTrans.app x) ≫
        (α.naturality g).hom.toNatTrans.app ((F.map f).toFunctor.obj x) ≫
          (G.map g).toFunctor.map ((α.naturality f).hom.toNatTrans.app x) := by
  cases h
  simpa only [Pseudofunctor.mapComp'_eq_mapComp] using
    natCompHomApp_comp (F := F) (G := G) α f g x

/-! ## 2. The componentwise associativity/cancellation -/

set_option pp.all false in
set_option pp.proofs false in
set_option pp.universes false in
/-- **The core component computation.**  For a strong transformation
`α : F ⟶ G` and composable site morphisms `y : X ⟶ S`, `q : X' ⟶ X` with
composite `z`, the conjugation of `u` by the naturality isomorphisms of `α`
commutes with the restrictions.  This is the componentwise
associativity/cancellation assembled from the three S1935 ingredients. -/
theorem S1988HComponent_naturality_core
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} (M N : F.obj (U S))
    {X X' : Site} (y : X ⟶ S) (z : X' ⟶ S) (q : X' ⟶ X)
    (hφ : y.op.toLoc ≫ q.op.toLoc = z.op.toLoc)
    (u : (F.map y.op.toLoc).toFunctor.obj M ⟶ (F.map y.op.toLoc).toFunctor.obj N) :
    (α.naturality z.op.toLoc).inv.toNatTrans.app M ≫
      (α.app (U X')).toFunctor.map
        ((F.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).hom.toNatTrans.app M) ≫
        (α.app (U X')).toFunctor.map
          ((F.map q.op.toLoc).toFunctor.map u) ≫
          (α.app (U X')).toFunctor.map
            ((F.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).inv.toNatTrans.app N) ≫
            (α.naturality z.op.toLoc).hom.toNatTrans.app N =
    (G.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).hom.toNatTrans.app
        ((α.app (U S)).toFunctor.obj M) ≫
      (G.map q.op.toLoc).toFunctor.map
        ((α.naturality y.op.toLoc).inv.toNatTrans.app M) ≫
        (G.map q.op.toLoc).toFunctor.map
          ((α.app (U X)).toFunctor.map u) ≫
          (G.map q.op.toLoc).toFunctor.map
            ((α.naturality y.op.toLoc).hom.toNatTrans.app N) ≫
          (G.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).inv.toNatTrans.app
            ((α.app (U S)).toFunctor.obj N) := by
  let eY := α.naturality (y.op.toLoc)
  let eZ := α.naturality (z.op.toLoc)
  let eQ := α.naturality (q.op.toLoc)
  let fX : ↑(F.obj (U X)) ⥤ ↑(G.obj (U X)) := (α.app (U X)).toFunctor
  let fX' : ↑(F.obj (U X')) ⥤ ↑(G.obj (U X')) := (α.app (U X')).toFunctor
  let fS : ↑(F.obj (U S)) ⥤ ↑(G.obj (U S)) := (α.app (U S)).toFunctor
  let Aq : ↑(F.obj (U X)) ⥤ ↑(F.obj (U X')) := (F.map q.op.toLoc).toFunctor
  let Cq : ↑(G.obj (U X)) ⥤ ↑(G.obj (U X')) := (G.map q.op.toLoc).toFunctor
  let AComp := F.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ
  let CComp := G.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ
  change eZ.inv.toNatTrans.app M ≫
      fX'.map (AComp.hom.toNatTrans.app M) ≫
        fX'.map (Aq.map u) ≫
          fX'.map (AComp.inv.toNatTrans.app N) ≫ eZ.hom.toNatTrans.app N =
    CComp.hom.toNatTrans.app (fS.obj M) ≫
      Cq.map (eY.inv.toNatTrans.app M) ≫
        Cq.map (fX.map u) ≫
          Cq.map (eY.hom.toNatTrans.app N) ≫
            CComp.inv.toNatTrans.app (fS.obj N)
  have hA := natCompInvApp_comp_mapComp' (F := F) (G := G)
    (α := α) (a := U S) (b := U X) (c := U X') (f := y.op.toLoc) (g := q.op.toLoc)
    (fg := z.op.toLoc) (h := hφ) (x := M)
  have hC := natCompHomApp_comp_mapComp' (F := F) (G := G)
    (α := α) (a := U S) (b := U X) (c := U X') (f := y.op.toLoc) (g := q.op.toLoc)
    (fg := z.op.toLoc) (h := hφ) (x := N)
  have hQ := eQ.inv.toNatTrans.naturality u
  have hAComp : AComp.inv.toNatTrans.app N ≫ AComp.hom.toNatTrans.app N = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, AComp.inv_hom_id, Cat.Hom₂.id_app]
  have hCComp : CComp.inv.toNatTrans.app (fS.obj N) ≫
      CComp.hom.toNatTrans.app (fS.obj N) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, CComp.inv_hom_id, Cat.Hom₂.id_app]
  have heQ : eQ.inv.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj N) ≫
      eQ.hom.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj N) = 𝟙 _ := by
    rw [← Cat.Hom₂.comp_app, eQ.inv_hom_id, Cat.Hom₂.id_app]
  have hmap : fX'.map (AComp.inv.toNatTrans.app N) ≫
      fX'.map (AComp.hom.toNatTrans.app N) = 𝟙 _ := by
    rw [← Functor.map_comp]
    rw [show AComp.inv.toNatTrans.app N ≫ AComp.hom.toNatTrans.app N = 𝟙 _ from hAComp]
    exact fX'.map_id _
  have hmap2 : fX'.map (AComp.inv.toNatTrans.app N) ≫
        fX'.map (AComp.hom.toNatTrans.app N) ≫
          eQ.hom.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj N) ≫
            Cq.map (eY.hom.toNatTrans.app N) =
      eQ.hom.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj N) ≫
        Cq.map (eY.hom.toNatTrans.app N) := by
    rw [← Category.assoc, hmap, Category.id_comp]
  have hW :
      eQ.inv.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj N) ≫
        fX'.map (AComp.inv.toNatTrans.app N) ≫ eZ.hom.toNatTrans.app N =
      Cq.map (eY.hom.toNatTrans.app N) ≫ CComp.inv.toNatTrans.app (fS.obj N) := by
    apply (cancel_mono (CComp.hom.toNatTrans.app (fS.obj N))).mp
    simp only [Category.assoc]
    rw [hC]
    rw [hmap2]
    rw [← Category.assoc, heQ, Category.id_comp]
    rw [hCComp]
    change Cq.map (eY.hom.toNatTrans.app N) =
      Cq.map (eY.hom.toNatTrans.app N) ≫
        𝟙 (Cq.obj ((G.map y.op.toLoc).toFunctor.obj (fS.obj N)))
    exact (Category.comp_id (Cq.map (eY.hom.toNatTrans.app N))).symm
  have hQ' : eQ.inv.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj M) ≫
        fX'.map (Aq.map u) =
      Cq.map (fX.map u) ≫
        eQ.inv.toNatTrans.app ((F.map y.op.toLoc).toFunctor.obj N) := by
    rw [← Functor.comp_map Aq fX' u, ← Functor.comp_map fX Cq u]
    exact hQ.symm
  slice_lhs 1 2 => rw [← hA]
  slice_lhs 3 4 => rw [hQ']
  slice_lhs 4 6 => rw [hW]

/-! ## 3. The generic component and its naturality -/

set_option pp.all false in
set_option pp.proofs false in
set_option pp.universes false in
/-- The generic H-comparison component: conjugate a section of the hom presheaf
of `F` by the naturality isomorphism of a strong transformation `α : F ⟶ G`. -/
noncomputable def S1988HComponent
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} (M N : F.obj (U S))
    (Y : (Over S)ᵒᵖ) (u : (F.presheafHom M N).obj Y) :
    (G.presheafHom ((α.app (U S)).toFunctor.obj M) ((α.app (U S)).toFunctor.obj N)).obj Y :=
  (α.naturality (Y.unop.hom.op.toLoc)).inv.toNatTrans.app M
    ≫ (α.app (U Y.unop.left)).toFunctor.map u
    ≫ (α.naturality (Y.unop.hom.op.toLoc)).hom.toNatTrans.app N

set_option pp.all false in
set_option pp.proofs false in
set_option pp.universes false in
/-- The component computation in the exact `pullHom` form: the generic
H-comparison is compatible with the restriction along a composable pair. -/
theorem S1988HComponent_pullHom
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} (M N : F.obj (U S))
    {X X' : Site} (y : X ⟶ S) (z : X' ⟶ S) (q : X' ⟶ X) (hq : q ≫ y = z)
    (u : (F.map y.op.toLoc).toFunctor.obj M ⟶ (F.map y.op.toLoc).toFunctor.obj N) :
    S1988HComponent α M N (Opposite.op (Over.mk z))
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          (F := F) u q z z) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := G) (S1988HComponent α M N (Opposite.op (Over.mk y)) u) q z z := by
  have hφ : y.op.toLoc ≫ q.op.toLoc = z.op.toLoc := by
    rw [← Quiver.Hom.comp_toLoc, ← CategoryTheory.op_comp, hq]
  unfold S1988HComponent
  simp only [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Functor.map_comp, Category.assoc]
  change (α.naturality z.op.toLoc).inv.toNatTrans.app M ≫
      (α.app (U X')).toFunctor.map
        ((F.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).hom.toNatTrans.app M) ≫
        (α.app (U X')).toFunctor.map
          ((F.map q.op.toLoc).toFunctor.map u) ≫
          (α.app (U X')).toFunctor.map
            ((F.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).inv.toNatTrans.app N) ≫
            (α.naturality z.op.toLoc).hom.toNatTrans.app N =
    (G.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).hom.toNatTrans.app
        ((α.app (U S)).toFunctor.obj M) ≫
      (G.map q.op.toLoc).toFunctor.map
        ((α.naturality y.op.toLoc).inv.toNatTrans.app M) ≫
        (G.map q.op.toLoc).toFunctor.map
          ((α.app (U X)).toFunctor.map u) ≫
          (G.map q.op.toLoc).toFunctor.map
            ((α.naturality y.op.toLoc).hom.toNatTrans.app N) ≫
          (G.mapComp' y.op.toLoc q.op.toLoc z.op.toLoc hφ).inv.toNatTrans.app
            ((α.app (U S)).toFunctor.obj N)
  exact S1988HComponent_naturality_core α M N y z q hφ u

set_option pp.all false in
set_option pp.proofs false in
set_option pp.universes false in
/-- **The generic naturality of the H-comparison component.**  For every strong
transformation `α : F ⟶ G`, every pair of objects and every morphism of
`Over S`, the generic component is natural with respect to the `pullHom`
restrictions on both sides. -/
theorem S1988HComponent_naturality
    {F G : Pseudofunctor (LocallyDiscrete Siteᵒᵖ) Cat.{0, 0}}
    (α : Pseudofunctor.StrongTrans F G) {S : Site} (M N : F.obj (U S))
    (Y Z : (Over S)ᵒᵖ) (p : Y ⟶ Z) (u : (F.presheafHom M N).obj Y) :
    S1988HComponent α M N Z ((F.presheafHom M N).map p u) =
      (G.presheafHom ((α.app (U S)).toFunctor.obj M) ((α.app (U S)).toFunctor.obj N)).map p
        (S1988HComponent α M N Y u) := by
  change S1988HComponent α M N (Opposite.op (Over.mk (Z.unop.hom)))
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := F) u (p.unop.left) (Z.unop.hom) (Z.unop.hom)) =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := G) (S1988HComponent α M N (Opposite.op (Over.mk (Y.unop.hom))) u)
      (p.unop.left) (Z.unop.hom) (Z.unop.hom)
  exact S1988HComponent_pullHom α M N (Y.unop.hom) (Z.unop.hom) (p.unop.left) (Over.w p.unop) u

/-! ## 4. The concrete H-comparisons and the exact first missing -/

section Concrete

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M N : IsoCommaObjAt f g S)

/-- The first concrete H-comparison is the generic component for `f.map`. -/
theorem S1956FstToHComponent_eq (Y : (Over S)ᵒᵖ)
    (u : (Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).obj Y) :
    S1956FstToHComponent f g M N Y u =
      S1988HComponent f.map M.obj.left N.obj.left Y u := rfl

/-- The second concrete H-comparison is the generic component for `g.map`
(the comparison `S1864SiteComparisonRight` is the inverse of the naturality
isomorphism, so its `hom`/`inv` swap matches the generic component). -/
theorem S1956SndToHComponent_eq (Y : (Over S)ᵒᵖ)
    (v : (Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).obj Y) :
    S1956SndToHComponent f g M N Y v =
      S1988HComponent g.map M.obj.right N.obj.right Y v := rfl

/-- **The first H-comparison is natural.** -/
theorem S1988FstToHNaturality : S1956FstToHNaturality f g M N := by
  intro Y Z p u
  rw [S1956FstToHComponent_eq f g M N Z, S1956FstToHComponent_eq f g M N Y]
  exact S1988HComponent_naturality f.map M.obj.left N.obj.left Y Z p u

/-- **The second H-comparison is natural.** -/
theorem S1988SndToHNaturality : S1956SndToHNaturality f g M N := by
  intro Y Z p v
  rw [S1956SndToHComponent_eq f g M N Z, S1956SndToHComponent_eq f g M N Y]
  exact S1988HComponent_naturality g.map M.obj.right N.obj.right Y Z p v

/-- **The exact first missing of S1970/S1956 is closed**: both H-comparisons are
natural. -/
theorem S1988HComparisonNaturality : S1956HComparisonNaturality f g M N :=
  ⟨S1988FstToHNaturality f g M N, S1988SndToHNaturality f g M N⟩

end Concrete

/-- **The uniform form of the exact first missing**: for every cospan, every
test object and every pair of iso-comma objects, the two H-comparisons are
natural. -/
theorem S1988HComparisonNaturalityAll : S1956HComparisonNaturalityAll := by
  intro A B C f g S M N
  exact S1988HComparisonNaturality f g M N

/-- **The S1970 form** of the exact first missing, definitionally the S1956
statement. -/
theorem S1988S1970HComparisonNaturalityAll : S1970HComparisonNaturalityAll :=
  S1988HComparisonNaturalityAll

/-- The consumer of S1970 specialized to the now-proved naturality: the two
H-comparisons assemble into natural transformations of hom presheaves. -/
theorem S1988HComparisonNaturalityAll_gives_natTrans :
    ∀ {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      {S : Site} (M N : IsoCommaObjAt f g S),
      Nonempty (Pseudofunctor.presheafHom A.source.fiber (S := S)
          M.obj.left N.obj.left ⟶
        Pseudofunctor.presheafHom C.source.fiber (S := S)
          ((f.map.app (U S)).toFunctor.obj M.obj.left)
          ((f.map.app (U S)).toFunctor.obj N.obj.left)) ∧
      Nonempty (Pseudofunctor.presheafHom B.source.fiber (S := S)
          M.obj.right N.obj.right ⟶
        Pseudofunctor.presheafHom C.source.fiber (S := S)
          ((g.map.app (U S)).toFunctor.obj M.obj.right)
          ((g.map.app (U S)).toFunctor.obj N.obj.right)) :=
  S1970HComparisonNaturalityAll_gives_natTrans S1988HComparisonNaturalityAll

/-! ## 5. The exact next missing (not asserted)

The prestack half is the statement `S1956IsoCommaPrestack f g`, i.e. the
sheaf condition for the hom presheaves of the iso-comma pseudofunctor.  Given
the naturality proved above, the remaining input is:

* the identification of `P.presheafHom M N` with the fibre product of the
  A-hom and B-hom presheaves over the C-hom presheaf, using the two H-comparison
  natural transformations, and
* the closure of `Presheaf.IsSheaf` under fibre products of `Type`-valued
  presheaves.

Neither is formalized in this file; the target `S1956IsoCommaPrestack` is
therefore still uninhabited.  The effectivity half `S1956IsoCommaEffectivity`
is likewise untouched. -/

/-- The exact next missing after this file: the prestack half for the actual
iso-comma pseudofunctor.  This is a named `Prop` with no inhabitant asserted. -/
def S1988NextMissingPrestack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  S1956IsoCommaPrestack f g

/-! ## 6. Checks and axiom audit -/

#check S1988HComponent_naturality_core
#check S1988HComponent
#check S1988HComponent_pullHom
#check S1988HComponent_naturality
#check S1956FstToHComponent_eq
#check S1956SndToHComponent_eq
#check S1988FstToHNaturality
#check S1988SndToHNaturality
#check S1988HComparisonNaturality
#check S1988HComparisonNaturalityAll
#check S1988S1970HComparisonNaturalityAll
#check S1988HComparisonNaturalityAll_gives_natTrans
#check S1988NextMissingPrestack

#print axioms S1988HComponent_naturality_core
#print axioms S1988HComponent
#print axioms S1988HComponent_pullHom
#print axioms S1988HComponent_naturality
#print axioms S1956FstToHComponent_eq
#print axioms S1956SndToHComponent_eq
#print axioms S1988FstToHNaturality
#print axioms S1988SndToHNaturality
#print axioms S1988HComparisonNaturality
#print axioms S1988HComparisonNaturalityAll
#print axioms S1988S1970HComparisonNaturalityAll
#print axioms S1988HComparisonNaturalityAll_gives_natTrans

end LeanFormal.IUT.XiFPaper.S1988HComparisonNaturalityActual
