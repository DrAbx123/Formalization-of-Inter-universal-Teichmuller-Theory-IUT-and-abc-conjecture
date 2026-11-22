/-
# S1956: IsStack for the actual iso-comma site pseudofunctor -- the exact first missing

## Context

S1945 constructed the actual category-valued pseudofunctor

  U |-> IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor)

on the etale site of `S1726K` for every cospan of actual finite-etale cover
maps `f : A -> C` and `g : B -> C`, using the restriction comparisons of
S1890 and S1935 and proving the three pseudofunctor coherence laws.  S1945
thereby closed S1864 (a).  The remaining descent item is S1864 (b):
`(sitePseudofunctor f g).IsStack J`.

The present file attacks (b).  It does **not** fake `IsStack`.

## What is proven unconditionally

1.  The decomposition of `IsStack` for the concrete pseudofunctor into the
    two fields of Mathlib's class: the prestack condition and the essential
    surjectivity of the comparison functor `toDescentData` for every covering
    sieve.  This is `S1956IsoCommaStack_iff_prestack_effectivity`.

2.  The two leg projections of the presheaf of morphisms.  For fixed objects
    `M N` of the iso-comma at a test object `S`, the first and second
    iso-comma projections give natural transformations

      P.presheafHom M N --> A.source.fiber.presheafHom M.left N.left
      P.presheafHom M N --> B.source.fiber.presheafHom M.right N.right.

    Their naturality is proved unconditionally
    (`S1956FstHomPresheaf`, `S1956SndHomPresheaf`).  This is the
    descent-of-morphisms part for the two legs.

3.  The candidate H-comparison maps.  The strong transformations
    `f.map` and `g.map` act on the F- and G-hom presheaves; composing with
    the naturality comparisons `S1864SiteComparisonLeft` and
    `S1864SiteComparisonRight` gives the two component functions
    `S1956FstToHComponent` and `S1956SndToHComponent`.  Their naturality is
    isolated exactly as `S1956FstToHNaturality` and
    `S1956SndToHNaturality`.

4.  The consumer to the S1864/S1891 obligation: `S1956IsoCommaStack f g`
    supplies the `stack` and `fiberEquiv` fields of S1891's existence form
    (and hence S1864's stack half) with the canonical pseudofunctor itself
    (`S1956IsoCommaStack_to_S1891`, `S1956IsoCommaStack_core`).

## The exact first missing

The first missing statement for the prestack half is the naturality of the
two H-comparison component functions:

  `S1956HComparisonNaturality f g M N`

(see `S1956FstToHNaturality` / `S1956SndToHNaturality`).  It is the
componentwise coherence of the strong transformations `f.map` and `g.map`
with the pseudofunctor comparison isomorphisms of `A.source.fiber`,
`B.source.fiber` and `C.source.fiber`, transported through the site
restrictions.  Once this naturality holds, the hom presheaf of the iso-comma
is the pullback of the F-, G- and H-hom presheaves; since the three corner
presheaves are sheaves (the three stacks are prestacks), the pullback is a
sheaf, and the iso-comma is a prestack.

The second missing statement is the effective-descent condition

  `S1956IsoCommaEffectivity f g`

i.e. essential surjectivity of `toDescentData` for every covering sieve.  It
is the object-level 2-limit interchange: a descent datum in the iso-comma is a
triple of descent data for F, G, H together with a comparison isomorphism in
the H-descent category, and the H-stack makes the comparison effective; the
resulting comma object is the required effective descent datum.

The passage from the H naturality to the prestack condition (the
pullback-of-sheaves argument described above) and the passage from the two
descent-data comparisons to effectivity are **not** formalized in this file.
They are the immediate next formal steps, not asserted theorems.

Neither `S1956HComparisonNaturalityAll` nor `S1956IsoCommaEffectivity` is
asserted.  The general theorem "the pointwise two-fibre product of three
stacks is a stack" is still not present in Mathlib; see S1891 for its exact
statement.

## Honest boundary

No `sorry`, no `axiom`, no `Shrink`, `ULift` or `PUnit`, and no fake
`IsStack`.  The only axioms used by the unconditional results are
`propext`, `Classical.choice` and `Quot.sound`; see the `#print axioms`
block at the end.
-/
import tmp.sheaf.xif.paper.S1945SitePseudofunctorDataActual
import tmp.sheaf.xif.paper.S1891PullbackStackIsStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual

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

universe u

abbrev K := S1726K
abbrev Site := SchemeOverField K
abbrev J : GrothendieckTopology Site := SchemeOverField.etaleTopology K

/-- The locally discrete test object of a scheme over the base field. -/
abbrev U (S : Site) : LocallyDiscrete Siteᵒᵖ :=
  LocallyDiscrete.mk (Opposite.op S)

/-- The value of the site pseudofunctor at a test object, written out. -/
abbrev IsoCommaObjAt {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (S : Site) :=
  S1836IsoComma (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor

/-! ## 1. The concrete `IsStack` target and its exact decomposition -/

/-- The prestack half for the actual iso-comma pseudofunctor. -/
def S1956IsoCommaPrestack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  (sitePseudofunctor f g).IsPrestack J

/-- The effective-descent half for the actual iso-comma pseudofunctor: the
comparison functor from the value at the base to descent data is essentially
surjective for every covering sieve. -/
def S1956IsoCommaEffectivity {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  ∀ (S : Site) (R : Sieve S), R ∈ J S →
    ((sitePseudofunctor f g).toDescentData
      (fun (i : R.arrows.category) => i.obj.hom)).EssSurj

/-- The stack condition for the actual iso-comma pseudofunctor.  This is the
S1864 (b) target.  It is a `Prop` with no inhabitant asserted in this file. -/
def S1956IsoCommaStack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  (sitePseudofunctor f g).IsStack J

/-- **The exact decomposition of the target.**  Mathlib's `IsStack` is the
conjunction of `IsPrestack` and essential surjectivity of `toDescentData` for
every covering sieve.  This theorem is unconditional and does not assert either
component. -/
theorem S1956IsoCommaStack_iff_prestack_effectivity
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1956IsoCommaStack f g ↔
      S1956IsoCommaPrestack f g ∧ S1956IsoCommaEffectivity f g := by
  constructor
  · intro h
    exact ⟨h.toIsPrestack, fun S R hR => h.essSurj_of_sieve R hR⟩
  · rintro ⟨hp, he⟩
    exact { toIsPrestack := hp, essSurj_of_sieve := fun {S} R hR => he S R hR }

/-- The prestack half is exactly the first missing component of the target. -/
theorem S1956IsoCommaPrestack_of_stack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1956IsoCommaStack f g) : S1956IsoCommaPrestack f g :=
  (S1956IsoCommaStack_iff_prestack_effectivity f g).1 h |>.1

/-- The effective-descent half is exactly the second missing component. -/
theorem S1956IsoCommaEffectivity_of_stack {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1956IsoCommaStack f g) : S1956IsoCommaEffectivity f g :=
  (S1956IsoCommaStack_iff_prestack_effectivity f g).1 h |>.2

/-! ## 2. The two leg projections of the hom presheaf -/

section Projections

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)

/-- The first projection of the composite comparison.  No coherence is assumed:
the projection of `mapComp'` is `mapComp'` of the first leg. -/
theorem S1956Fst_mapComp' {U V W : LocallyDiscrete Siteᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) (χ : U ⟶ W) (h : φ ≫ ψ = χ)
    (X : ↑((sitePseudofunctor f g).obj U)) :
    (S1836IsoCommaFst (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        (((sitePseudofunctor f g).mapComp' φ ψ χ h).hom.toNatTrans.app X) =
      (A.source.fiber.mapComp' φ ψ χ h).hom.toNatTrans.app X.obj.left := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The first projection of the inverse composite comparison. -/
theorem S1956Fst_mapComp'_inv {U V W : LocallyDiscrete Siteᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) (χ : U ⟶ W) (h : φ ≫ ψ = χ)
    (X : ↑((sitePseudofunctor f g).obj U)) :
    (S1836IsoCommaFst (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        (((sitePseudofunctor f g).mapComp' φ ψ χ h).inv.toNatTrans.app X) =
      (A.source.fiber.mapComp' φ ψ χ h).inv.toNatTrans.app X.obj.left := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The first projection is strictly compatible with the site restriction. -/
theorem S1956Fst_map {U V : LocallyDiscrete Siteᵒᵖ}
    (φ : U ⟶ V) {X Y : ↑((sitePseudofunctor f g).obj U)} (m : X ⟶ Y) :
    (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        (((sitePseudofunctor f g).map φ).toFunctor.map m) =
      (A.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaFst (f.map.app U).toFunctor (g.map.app U).toFunctor).map m) := by
  change (S1836IsoCommaFst (f.map.app V).toFunctor (g.map.app V).toFunctor).map
      ((S1890IsoCommaMap f g φ).toFunctor.map m) = _
  rfl

/-- **The first leg projection of the hom presheaf.**  It is natural by the
three component lemmas above. -/
noncomputable def S1956FstHomPresheaf {S : Site}
    (M N : IsoCommaObjAt f g S) :
    Pseudofunctor.presheafHom (sitePseudofunctor f g) M N ⟶
      Pseudofunctor.presheafHom A.source.fiber (S := S)
        ((S1836IsoCommaFst (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor).obj M)
        ((S1836IsoCommaFst (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor).obj N) where
  app Y := ↾fun φ => by
    change ((sitePseudofunctor f g).map ((Opposite.unop Y).hom.op.toLoc)).toFunctor.obj M ⟶
      ((sitePseudofunctor f g).map ((Opposite.unop Y).hom.op.toLoc)).toFunctor.obj N at φ
    exact (S1836IsoCommaFst (f.map.app (U (Opposite.unop Y).left)).toFunctor
      (g.map.app (U (Opposite.unop Y).left)).toFunctor).map φ
  naturality {Y Z} p := by
    ext φ
    change (S1836IsoCommaFst (f.map.app (U (Opposite.unop Z).left)).toFunctor
        (g.map.app (U (Opposite.unop Z).left)).toFunctor).map
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := sitePseudofunctor f g)
        φ p.unop.left Z.unop.hom Z.unop.hom) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := A.source.fiber)
        ((S1836IsoCommaFst (f.map.app (U (Opposite.unop Y).left)).toFunctor
          (g.map.app (U (Opposite.unop Y).left)).toFunctor).map φ)
        p.unop.left Z.unop.hom Z.unop.hom
    simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp, Category.assoc]
    rw [S1956Fst_mapComp', S1956Fst_map, S1956Fst_mapComp'_inv]

/-- The second projection of the composite comparison. -/
theorem S1956Snd_mapComp' {U V W : LocallyDiscrete Siteᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) (χ : U ⟶ W) (h : φ ≫ ψ = χ)
    (X : ↑((sitePseudofunctor f g).obj U)) :
    (S1836IsoCommaSnd (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        (((sitePseudofunctor f g).mapComp' φ ψ χ h).hom.toNatTrans.app X) =
      (B.source.fiber.mapComp' φ ψ χ h).hom.toNatTrans.app X.obj.right := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The second projection of the inverse composite comparison. -/
theorem S1956Snd_mapComp'_inv {U V W : LocallyDiscrete Siteᵒᵖ}
    (φ : U ⟶ V) (ψ : V ⟶ W) (χ : U ⟶ W) (h : φ ≫ ψ = χ)
    (X : ↑((sitePseudofunctor f g).obj U)) :
    (S1836IsoCommaSnd (f.map.app W).toFunctor (g.map.app W).toFunctor).map
        (((sitePseudofunctor f g).mapComp' φ ψ χ h).inv.toNatTrans.app X) =
      (B.source.fiber.mapComp' φ ψ χ h).inv.toNatTrans.app X.obj.right := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp, Pseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- The second projection is strictly compatible with the site restriction. -/
theorem S1956Snd_map {U V : LocallyDiscrete Siteᵒᵖ}
    (φ : U ⟶ V) {X Y : ↑((sitePseudofunctor f g).obj U)} (m : X ⟶ Y) :
    (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
        (((sitePseudofunctor f g).map φ).toFunctor.map m) =
      (B.source.fiber.map φ).toFunctor.map
        ((S1836IsoCommaSnd (f.map.app U).toFunctor (g.map.app U).toFunctor).map m) := by
  change (S1836IsoCommaSnd (f.map.app V).toFunctor (g.map.app V).toFunctor).map
      ((S1890IsoCommaMap f g φ).toFunctor.map m) = _
  rfl

/-- **The second leg projection of the hom presheaf.** -/
noncomputable def S1956SndHomPresheaf {S : Site}
    (M N : IsoCommaObjAt f g S) :
    Pseudofunctor.presheafHom (sitePseudofunctor f g) M N ⟶
      Pseudofunctor.presheafHom B.source.fiber (S := S)
        ((S1836IsoCommaSnd (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor).obj M)
        ((S1836IsoCommaSnd (f.map.app (U S)).toFunctor (g.map.app (U S)).toFunctor).obj N) where
  app Y := ↾fun φ => by
    change ((sitePseudofunctor f g).map ((Opposite.unop Y).hom.op.toLoc)).toFunctor.obj M ⟶
      ((sitePseudofunctor f g).map ((Opposite.unop Y).hom.op.toLoc)).toFunctor.obj N at φ
    exact (S1836IsoCommaSnd (f.map.app (U (Opposite.unop Y).left)).toFunctor
      (g.map.app (U (Opposite.unop Y).left)).toFunctor).map φ
  naturality {Y Z} p := by
    ext φ
    change (S1836IsoCommaSnd (f.map.app (U (Opposite.unop Z).left)).toFunctor
        (g.map.app (U (Opposite.unop Z).left)).toFunctor).map
      (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := sitePseudofunctor f g)
        φ p.unop.left Z.unop.hom Z.unop.hom) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := B.source.fiber)
        ((S1836IsoCommaSnd (f.map.app (U (Opposite.unop Y).left)).toFunctor
          (g.map.app (U (Opposite.unop Y).left)).toFunctor).map φ)
        p.unop.left Z.unop.hom Z.unop.hom
    simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.map_comp, Category.assoc]
    rw [S1956Snd_mapComp', S1956Snd_map, S1956Snd_mapComp'_inv]

end Projections

/-! ## 3. The H-comparison and the exact first missing -/

section HComparison

variable {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
  {S : Site} (M N : IsoCommaObjAt f g S)

/-- The candidate H-comparison map from the first leg: apply the first cover
map, using the naturality comparison of the strong transformation. -/
noncomputable def S1956FstToHComponent (Y : (Over S)ᵒᵖ)
    (u : (Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).obj Y) :
    (Pseudofunctor.presheafHom C.source.fiber (S := S)
      ((f.map.app (U S)).toFunctor.obj M.obj.left)
      ((f.map.app (U S)).toFunctor.obj N.obj.left)).obj Y :=
  (S1864SiteComparisonLeft f ((Opposite.unop Y).hom.op.toLoc)).inv.app M.obj.left
    ≫ (f.map.app (U (Opposite.unop Y).left)).toFunctor.map u
    ≫ (S1864SiteComparisonLeft f ((Opposite.unop Y).hom.op.toLoc)).hom.app N.obj.left

/-- The candidate H-comparison map from the second leg. -/
noncomputable def S1956SndToHComponent (Y : (Over S)ᵒᵖ)
    (v : (Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).obj Y) :
    (Pseudofunctor.presheafHom C.source.fiber (S := S)
      ((g.map.app (U S)).toFunctor.obj M.obj.right)
      ((g.map.app (U S)).toFunctor.obj N.obj.right)).obj Y :=
  (S1864SiteComparisonRight g ((Opposite.unop Y).hom.op.toLoc)).hom.app M.obj.right
    ≫ (g.map.app (U (Opposite.unop Y).left)).toFunctor.map v
    ≫ (S1864SiteComparisonRight g ((Opposite.unop Y).hom.op.toLoc)).inv.app N.obj.right

/-- **The exact first missing naturality** of the first-leg H-comparison.  This
is the componentwise coherence of `f.map` with the pseudofunctor comparisons
of the three stacks, transported through the site restrictions. -/
def S1956FstToHNaturality : Prop :=
  ∀ (Y Z : (Over S)ᵒᵖ) (p : Y ⟶ Z)
    (u : (Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).obj Y),
    S1956FstToHComponent f g M N Z
        ((Pseudofunctor.presheafHom A.source.fiber (S := S) M.obj.left N.obj.left).map p u) =
      (Pseudofunctor.presheafHom C.source.fiber (S := S)
        ((f.map.app (U S)).toFunctor.obj M.obj.left)
        ((f.map.app (U S)).toFunctor.obj N.obj.left)).map p
        (S1956FstToHComponent f g M N Y u)

/-- **The exact first missing naturality** of the second-leg H-comparison. -/
def S1956SndToHNaturality : Prop :=
  ∀ (Y Z : (Over S)ᵒᵖ) (p : Y ⟶ Z)
    (v : (Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).obj Y),
    S1956SndToHComponent f g M N Z
        ((Pseudofunctor.presheafHom B.source.fiber (S := S) M.obj.right N.obj.right).map p v) =
      (Pseudofunctor.presheafHom C.source.fiber (S := S)
        ((g.map.app (U S)).toFunctor.obj M.obj.right)
        ((g.map.app (U S)).toFunctor.obj N.obj.right)).map p
        (S1956SndToHComponent f g M N Y v)

/-- The two H-comparison naturalities together. -/
def S1956HComparisonNaturality : Prop :=
  S1956FstToHNaturality f g M N ∧ S1956SndToHNaturality f g M N

/-- The first missing for the prestack half, uniformly over all cospans and
all test objects.  This is a named `Prop` with no inhabitant asserted. -/
def S1956HComparisonNaturalityAll : Prop :=
  ∀ {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    {S : Site} (M N : IsoCommaObjAt f g S),
    S1956HComparisonNaturality f g M N

end HComparison

/-! ## 4. Consumers and the exact state of the obligation -/

/-- **The concrete target supplies S1891's existence form** with the canonical
pseudofunctor `sitePseudofunctor f g` itself, not merely with an unspecified
witness.  This is the sense in which it fills the `stack` and
`fiberEquiv` fields of S1864's obligation. -/
theorem S1956IsoCommaStack_to_S1891 {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1956IsoCommaStack f g) :
    S1891IsoCommaStackExistsFor J A.source.fiber B.source.fiber C.source.fiber
      f.map g.map := by
  refine ⟨sitePseudofunctor f g, h, fun U => ⟨?_⟩⟩
  exact CategoryTheory.Equivalence.refl

/-- **The concrete target supplies S1864's stack half** (S1891's core
statement) for the canonical witness. -/
theorem S1956IsoCommaStack_core {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1956IsoCommaStack f g) :
    S1891IsoCommaStackCore f g :=
  S1891IsoCommaStackCore_iff_existsFor.2 (S1956IsoCommaStack_to_S1891 f g h)

/-- The target in the exact form of S1864 (b): the `stack` field of the
iso-comma obligation is inhabited by the canonical pseudofunctor as soon as
`S1956IsoCommaStack` holds.  This is a `Prop`-level reduction, not an
assertion of the target. -/
theorem S1956IsoCommaStack_gives_stack_field {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (h : S1956IsoCommaStack f g) :
    ∃ stack : EtaleStackOverField K,
      stack.fiber = sitePseudofunctor f g ∧
        stack.fiber.IsStack J ∧
          ∀ U : LocallyDiscrete Siteᵒᵖ,
            Nonempty (↑(stack.fiber.obj U) ≌
              S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor) := by
  refine ⟨{ fiber := sitePseudofunctor f g, isStack := h }, rfl, h, fun U => ⟨?_⟩⟩
  exact CategoryTheory.Equivalence.refl

/-! ## 5. Checks and axiom audit -/

#check S1956IsoCommaPrestack
#check S1956IsoCommaEffectivity
#check S1956IsoCommaStack
#check S1956IsoCommaStack_iff_prestack_effectivity
#check S1956IsoCommaPrestack_of_stack
#check S1956IsoCommaEffectivity_of_stack
#check S1956Fst_mapComp'
#check S1956Fst_mapComp'_inv
#check S1956Fst_map
#check S1956FstHomPresheaf
#check S1956Snd_mapComp'
#check S1956Snd_mapComp'_inv
#check S1956Snd_map
#check S1956SndHomPresheaf
#check S1956FstToHComponent
#check S1956SndToHComponent
#check S1956FstToHNaturality
#check S1956SndToHNaturality
#check S1956HComparisonNaturality
#check S1956HComparisonNaturalityAll
#check S1956IsoCommaStack_to_S1891
#check S1956IsoCommaStack_core
#check S1956IsoCommaStack_gives_stack_field

#print axioms S1956IsoCommaStack_iff_prestack_effectivity
#print axioms S1956IsoCommaPrestack_of_stack
#print axioms S1956IsoCommaEffectivity_of_stack
#print axioms S1956Fst_mapComp'
#print axioms S1956Fst_mapComp'_inv
#print axioms S1956Fst_map
#print axioms S1956FstHomPresheaf
#print axioms S1956Snd_mapComp'
#print axioms S1956Snd_mapComp'_inv
#print axioms S1956Snd_map
#print axioms S1956SndHomPresheaf
#print axioms S1956FstToHComponent
#print axioms S1956SndToHComponent
#print axioms S1956IsoCommaStack_to_S1891
#print axioms S1956IsoCommaStack_core
#print axioms S1956IsoCommaStack_gives_stack_field

end LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
