/-
# S1893: the 2-fibre product universal property of the iso-comma

## Context

S1864 isolated four missing items for the general-cospan pseudopullback; item (d)
is the *universal property* of the 2-fibre product together with the essential
surjectivity of the canonical comparison.  S1864 constructed the fibre-level
iso-comma `S1836IsoComma L R`, its two projections, and the canonical comparison
`S1864ConeFunctor`, but did not show that the iso-comma actually has the
universal property.

## What is proved here (unconditionally, no sorry, no new axiom)

1.  The category of pseudo-cones `S1893Cone L R X` over the cospan
    `L : A ⥤ C`, `R : B ⥤ C` with apex `X`.  A morphism of cones is a pair of
    2-cells compatible with the two structure isomorphisms (a *genuine* 2-cell of
    the cone category, not a projection-only datum).

2.  The comparison functor

      `S1893ComparisonFunctor L R X : (X ⥤ S1836IsoComma L R) ⥤ S1893Cone L R X`

    sending a functor `F` to the cone `(F ⋙ fst, F ⋙ snd, F ⋙ δ)`, where
    `δ = S1836IsoCommaNatIso L R`.  It is proved full, faithful and essentially
    surjective, hence an equivalence.  This is the 2-categorical universal
    property of the iso-comma: the iso-comma *is* the 2-fibre product.

3.  The universal-property data of S1832's two-pullback, at the level of the
    iso-comma apex:

    * `S1893Lift c`      := `S1864ConeFunctor L R c.toA c.toB c.commutes`;
    * `S1893LiftToA c`   : `Iso (S1893Lift c ⋙ fst) c.toA`  (strict: `rfl`);
    * `S1893LiftToB c`   : `Iso (S1893Lift c ⋙ snd) c.toB`  (strict: `rfl`);
    * `S1893LiftUniq`    : any 1-cell `F` into the iso-comma whose *cone* (with
      the comparison 2-cells) is isomorphic to `c` is isomorphic to the lift;
    * `S1893Lift_structure` : the structure 2-cell of the lift is the structure
      2-cell of the cone (no fake 2-cell is inserted anywhere).

    The uniqueness hypothesis is the honest one: an isomorphism in the *cone
    category*, i.e. a comparison 2-cell compatible with the structure
    isomorphisms.  The projection-only version is false (S1801 records the
    counterexample for the recorded witness, and the same phenomenon occurs for
    the iso-comma: two 1-cells with isomorphic projections can differ in the
    comparison 2-cell).

4.  The canonical comparison is an equivalence.  For a cone `c` with apex `X`
    together with a functor `F : X ⥤ IsoComma` and an isomorphism of cones
    `Φ(F) ≅ c`, the canonical comparison `S1893Lift c` is isomorphic to `F`; in
    particular, if `F` is an equivalence (e.g. the fibre realization of an actual
    two-pullback apex) then the canonical comparison is an equivalence.  The
    universal cone of the iso-comma itself gives the self-realization statement:
    the canonical comparison of `S1893UniversalCone` is an equivalence.

## The precise first missing at the site level

Everything here is at the level of *categories*: it is the fibre of the
would-be pseudopullback stack at one test object.  To obtain the stack-level
fields `lift / liftCommutes / liftToA / liftToB / uniq` of S1864's obligation,
the fibre-level functors must be assembled into a *strong transformation*
`W.source.fiber ⥤ P.apex.source.fiber`.  A strong transformation requires, for
every morphism `φ : U ⟶ V` of test objects, a naturality isomorphism

    `(W.fiber.map φ) ⋙ (fibrewise lift at U)  ≅  (fibrewise lift at V) ⋙ (P.fiber.map φ)`,

coherent with identities and composites.  These comparisons are exactly the
pseudofunctor comparison isomorphisms (mapId / mapComp) of the iso-comma
pseudofunctor `U ↦ S1836IsoComma (f.app U) (g.app U)` -- S1864 item (a).  They
are not constructed in the tree, and the fibre-level universal property proved
here does not produce them (there is no map on the site in the fibre data).
Thus item (d) is *reduced* to item (a): the first missing statement for (d) is
the pseudofunctor coherence of the iso-comma, exactly as S1864 records.

## Axiom footprint

Only `propext`, `Classical.choice` and `Quot.sound` (checked in the `#print
axioms` block at the end).  No sorry, no new axiom, no Shrink/ULift/PUnit.
-/
import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual

universe u

section Basic

variable {A B C : Type u} [Category.{u, u} A] [Category.{u, u} B] [Category.{u, u} C]

structure S1893Cone (L : A ⥤ C) (R : B ⥤ C) (X : Type u) [Category.{u, u} X] :
    Type u where
  toA : X ⥤ A
  toB : X ⥤ B
  commutes : Iso (toA ⋙ L) (toB ⋙ R)

namespace S1893Cone

variable {L : A ⥤ C} {R : B ⥤ C} {X : Type u} [Category.{u, u} X]

abbrev Hom (c₁ c₂ : S1893Cone L R X) : Type u :=
  { p : (c₁.toA ⟶ c₂.toA) × (c₁.toB ⟶ c₂.toB) //
    Functor.whiskerRight p.1 L ≫ c₂.commutes.hom =
      c₁.commutes.hom ≫ Functor.whiskerRight p.2 R }

abbrev Hom.toA {c₁ c₂ : S1893Cone L R X} (m : Hom c₁ c₂) : c₁.toA ⟶ c₂.toA :=
  m.1.1

abbrev Hom.toB {c₁ c₂ : S1893Cone L R X} (m : Hom c₁ c₂) : c₁.toB ⟶ c₂.toB :=
  m.1.2

theorem Hom.compatible_app {c₁ c₂ : S1893Cone L R X} (m : Hom c₁ c₂) (x : X) :
    L.map (m.toA.app x) ≫ (c₂.commutes.hom.app x) =
      (c₁.commutes.hom.app x) ≫ R.map (m.toB.app x) := by
  have h := NatTrans.congr_app m.2 x
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app] using h

@[ext]
theorem Hom.ext {c₁ c₂ : S1893Cone L R X} {f g : Hom c₁ c₂}
    (h₁ : f.toA = g.toA) (h₂ : f.toB = g.toB) : f = g :=
  Subtype.ext (Prod.ext h₁ h₂)

instance : Category.{u, u} (S1893Cone L R X) where
  Hom := Hom
  id := fun c => ⟨(𝟙 c.toA, 𝟙 c.toB), by
    show Functor.whiskerRight (𝟙 c.toA) L ≫ c.commutes.hom =
      c.commutes.hom ≫ Functor.whiskerRight (𝟙 c.toB) R
    rw [Functor.whiskerRight_id', Functor.whiskerRight_id']
    simp⟩
  comp := fun {c₁ c₂ c₃} m₁ m₂ => ⟨(m₁.toA ≫ m₂.toA, m₁.toB ≫ m₂.toB), by
    have h₁ := m₁.2
    have h₂ := m₂.2
    show Functor.whiskerRight (m₁.toA ≫ m₂.toA) L ≫ c₃.commutes.hom =
      c₁.commutes.hom ≫ Functor.whiskerRight (m₁.toB ≫ m₂.toB) R
    rw [Functor.whiskerRight_comp, Functor.whiskerRight_comp, Category.assoc, h₂,
      ← Category.assoc, h₁, Category.assoc, ← Functor.whiskerRight_comp]⟩
  id_comp := fun {c₁ c₂} m => Hom.ext
    (by
      show (𝟙 c₁.toA) ≫ m.toA = m.toA
      simp)
    (by
      show (𝟙 c₁.toB) ≫ m.toB = m.toB
      simp)
  comp_id := fun {c₁ c₂} m => Hom.ext
    (by
      show m.toA ≫ (𝟙 c₂.toA) = m.toA
      simp)
    (by
      show m.toB ≫ (𝟙 c₂.toB) = m.toB
      simp)
  assoc := fun {c₁ c₂ c₃ c₄} m₁ m₂ m₃ => Hom.ext
    (by
      show (m₁.toA ≫ m₂.toA) ≫ m₃.toA = m₁.toA ≫ m₂.toA ≫ m₃.toA
      simp)
    (by
      show (m₁.toB ≫ m₂.toB) ≫ m₃.toB = m₁.toB ≫ m₂.toB ≫ m₃.toB
      simp)

end S1893Cone

noncomputable def S1893Cone.forgetA (L : A ⥤ C) (R : B ⥤ C) (X : Type u)
    [Category.{u, u} X] : S1893Cone L R X ⥤ (X ⥤ A) where
  obj c := c.toA
  map m := m.toA
  map_id c := rfl
  map_comp m₁ m₂ := rfl

noncomputable def S1893Cone.forgetB (L : A ⥤ C) (R : B ⥤ C) (X : Type u)
    [Category.{u, u} X] : S1893Cone L R X ⥤ (X ⥤ B) where
  obj c := c.toB
  map m := m.toB
  map_id c := rfl
  map_comp m₁ m₂ := rfl

variable (L : A ⥤ C) (R : B ⥤ C)

@[simp]
theorem S1836IsoCommaNatIso_hom_app {Z : S1836IsoComma L R} :
    (S1836IsoCommaNatIso L R).hom.app Z = Z.obj.hom := rfl

noncomputable def S1893ComparisonCommutes {X : Type u} [Category.{u, u} X]
    (F : X ⥤ S1836IsoComma L R) :
    Iso ((F ⋙ S1836IsoCommaFst L R) ⋙ L) ((F ⋙ S1836IsoCommaSnd L R) ⋙ R) :=
  NatIso.ofComponents
    (fun x => (S1836IsoCommaNatIso L R).app (F.obj x))
    (fun {x y} f => (S1836IsoCommaNatIso L R).hom.naturality (F.map f))

@[simp]
theorem S1893ComparisonCommutes_hom_app {X : Type u} [Category.{u, u} X]
    (F : X ⥤ S1836IsoComma L R) (x : X) :
    (S1893ComparisonCommutes L R F).hom.app x =
      (S1836IsoCommaNatIso L R).hom.app (F.obj x) := rfl

theorem S1893ComparisonCommutes_naturality {X : Type u} [Category.{u, u} X]
    {F G : X ⥤ S1836IsoComma L R} (φ : F ⟶ G) (x : X) :
    (Functor.whiskerRight (Functor.whiskerRight φ (S1836IsoCommaFst L R)) L).app x ≫
        (S1893ComparisonCommutes L R G).hom.app x =
      (S1893ComparisonCommutes L R F).hom.app x ≫
        (Functor.whiskerRight (Functor.whiskerRight φ (S1836IsoCommaSnd L R)) R).app x := by
  simpa only [Functor.whiskerRight_app, Functor.comp_map, S1893ComparisonCommutes_hom_app]
    using (S1836IsoCommaNatIso L R).hom.naturality (φ.app x)

noncomputable def S1893ComparisonFunctor (X : Type u) [Category.{u, u} X] :
    (X ⥤ S1836IsoComma L R) ⥤ S1893Cone L R X where
  obj F :=
    { toA := F ⋙ S1836IsoCommaFst L R
      toB := F ⋙ S1836IsoCommaSnd L R
      commutes := S1893ComparisonCommutes L R F }
  map {F G} φ :=
    ⟨(Functor.whiskerRight φ (S1836IsoCommaFst L R),
      Functor.whiskerRight φ (S1836IsoCommaSnd L R)), by
        show Functor.whiskerRight (Functor.whiskerRight φ (S1836IsoCommaFst L R)) L ≫
            (S1893ComparisonCommutes L R G).hom =
          (S1893ComparisonCommutes L R F).hom ≫
            Functor.whiskerRight (Functor.whiskerRight φ (S1836IsoCommaSnd L R)) R
        apply NatTrans.ext
        funext x
        exact S1893ComparisonCommutes_naturality L R φ x⟩
  map_id F := by
    apply S1893Cone.Hom.ext
    · show Functor.whiskerRight (𝟙 F) (S1836IsoCommaFst L R) =
        𝟙 (F ⋙ S1836IsoCommaFst L R)
      rw [Functor.whiskerRight_id']
    · show Functor.whiskerRight (𝟙 F) (S1836IsoCommaSnd L R) =
        𝟙 (F ⋙ S1836IsoCommaSnd L R)
      rw [Functor.whiskerRight_id']
  map_comp φ ψ := by
    apply S1893Cone.Hom.ext
    · show Functor.whiskerRight (φ ≫ ψ) (S1836IsoCommaFst L R) =
        Functor.whiskerRight φ (S1836IsoCommaFst L R) ≫
          Functor.whiskerRight ψ (S1836IsoCommaFst L R)
      rw [Functor.whiskerRight_comp]
    · show Functor.whiskerRight (φ ≫ ψ) (S1836IsoCommaSnd L R) =
        Functor.whiskerRight φ (S1836IsoCommaSnd L R) ≫
          Functor.whiskerRight ψ (S1836IsoCommaSnd L R)
      rw [Functor.whiskerRight_comp]

@[simp]
theorem S1893ComparisonFunctor_obj_commutes_hom_app (X : Type u) [Category.{u, u} X]
    (F : X ⥤ S1836IsoComma L R) (x : X) :
    ((S1893ComparisonFunctor L R X).obj F).commutes.hom.app x =
      (S1836IsoCommaNatIso L R).hom.app (F.obj x) := rfl

instance S1893ComparisonFunctor_faithful (X : Type u) [Category.{u, u} X] :
    (S1893ComparisonFunctor L R X).Faithful where
  map_injective {F G} {φ ψ} h := by
    have hA : Functor.whiskerRight φ (S1836IsoCommaFst L R) =
        Functor.whiskerRight ψ (S1836IsoCommaFst L R) := congrArg (fun m => m.toA) h
    have hB : Functor.whiskerRight φ (S1836IsoCommaSnd L R) =
        Functor.whiskerRight ψ (S1836IsoCommaSnd L R) := congrArg (fun m => m.toB) h
    apply NatTrans.ext
    funext x
    apply S1836IsoComma_hom_ext L R
    · exact congrArg (fun α => α.app x) hA
    · exact congrArg (fun α => α.app x) hB

instance S1893ComparisonFunctor_full (X : Type u) [Category.{u, u} X] :
    (S1893ComparisonFunctor L R X).Full where
  map_surjective {F G} m := by
    let φ : F ⟶ G :=
      { app := fun x =>
          ObjectProperty.homMk (P := fun Y : Comma L R => IsIso Y.hom)
            (CommaMorphism.mk (m.toA.app x) (m.toB.app x) (by
              have h := S1893Cone.Hom.compatible_app m x
              have eF : ((S1893ComparisonFunctor L R X).obj F).commutes.hom.app x =
                  (S1836IsoCommaNatIso L R).hom.app (F.obj x) := rfl
              have eG : ((S1893ComparisonFunctor L R X).obj G).commutes.hom.app x =
                  (S1836IsoCommaNatIso L R).hom.app (G.obj x) := rfl
              have hF : (S1836IsoCommaNatIso L R).hom.app (F.obj x) = (F.obj x).obj.hom := rfl
              have hG : (S1836IsoCommaNatIso L R).hom.app (G.obj x) = (G.obj x).obj.hom := rfl
              rw [eF, eG, hF, hG] at h
              exact h))
        naturality := by
          intro x y f
          apply ObjectProperty.hom_ext
          apply Comma.hom_ext
          · exact m.toA.naturality f
          · exact m.toB.naturality f }
    refine ⟨φ, ?_⟩
    apply S1893Cone.Hom.ext
    · apply NatTrans.ext
      funext x
      rfl
    · apply NatTrans.ext
      funext x
      rfl

variable {X : Type u} [Category.{u, u} X]

noncomputable def S1893Lift (c : S1893Cone L R X) : X ⥤ S1836IsoComma L R :=
  S1864ConeFunctor L R c.toA c.toB c.commutes

theorem S1893Lift_fst (c : S1893Cone L R X) :
    S1893Lift L R c ⋙ S1836IsoCommaFst L R = c.toA := rfl

theorem S1893Lift_snd (c : S1893Cone L R X) :
    S1893Lift L R c ⋙ S1836IsoCommaSnd L R = c.toB := rfl

@[simp]
theorem S1893Lift_structure (c : S1893Cone L R X) (x : X) :
    ((S1893Lift L R c).obj x).obj.hom = (c.commutes.app x).hom :=
  S1864ConeFunctor_obj_hom L R c.toA c.toB c.commutes x

@[simp]
theorem S1893Lift_obj_fst (c : S1893Cone L R X) (x : X) :
    (S1836IsoCommaFst L R).obj ((S1893Lift L R c).obj x) = c.toA.obj x := rfl

@[simp]
theorem S1893Lift_obj_snd (c : S1893Cone L R X) (x : X) :
    (S1836IsoCommaSnd L R).obj ((S1893Lift L R c).obj x) = c.toB.obj x := rfl

@[simp]
theorem S1893Lift_map_fst (c : S1893Cone L R X) {x y : X} (f : x ⟶ y) :
    (S1836IsoCommaFst L R).map ((S1893Lift L R c).map f) = c.toA.map f := rfl

@[simp]
theorem S1893Lift_map_snd (c : S1893Cone L R X) {x y : X} (f : x ⟶ y) :
    (S1836IsoCommaSnd L R).map ((S1893Lift L R c).map f) = c.toB.map f := rfl

noncomputable def S1893LiftToA (c : S1893Cone L R X) :
    Iso (S1893Lift L R c ⋙ S1836IsoCommaFst L R) c.toA :=
  Iso.refl c.toA

noncomputable def S1893LiftToB (c : S1893Cone L R X) :
    Iso (S1893Lift L R c ⋙ S1836IsoCommaSnd L R) c.toB :=
  Iso.refl c.toB

theorem S1893ComparisonFunctor_obj_lift_commutes_hom (c : S1893Cone L R X) :
    ((S1893ComparisonFunctor L R X).obj
        (S1864ConeFunctor L R c.toA c.toB c.commutes)).commutes.hom = c.commutes.hom := by
  apply NatTrans.ext
  funext x
  have h1 : ((S1893ComparisonFunctor L R X).obj
      (S1864ConeFunctor L R c.toA c.toB c.commutes)).commutes.hom.app x =
      (S1836IsoCommaNatIso L R).hom.app
        ((S1864ConeFunctor L R c.toA c.toB c.commutes).obj x) := rfl
  have h2 : (S1836IsoCommaNatIso L R).hom.app
      ((S1864ConeFunctor L R c.toA c.toB c.commutes).obj x) =
      ((S1864ConeFunctor L R c.toA c.toB c.commutes).obj x).obj.hom := rfl
  have h3 : ((S1864ConeFunctor L R c.toA c.toB c.commutes).obj x).obj.hom =
      (c.commutes.app x).hom := S1864ConeFunctor_obj_hom L R c.toA c.toB c.commutes x
  have h4 : (c.commutes.app x).hom = c.commutes.hom.app x := Iso.app_hom c.commutes x
  exact h1.trans (h2.trans (h3.trans h4))

theorem S1893ComparisonFunctor_obj_lift_eq (c : S1893Cone L R X) :
    (S1893ComparisonFunctor L R X).obj
        (S1864ConeFunctor L R c.toA c.toB c.commutes) = c := by
  obtain ⟨a, b, γ⟩ := c
  have hγ : ((S1893ComparisonFunctor L R X).obj
      (S1864ConeFunctor L R a b γ)).commutes = γ := by
    apply Iso.ext
    apply NatTrans.ext
    funext x
    have h1 : ((S1893ComparisonFunctor L R X).obj
        (S1864ConeFunctor L R a b γ)).commutes.hom.app x =
        (S1836IsoCommaNatIso L R).hom.app
          ((S1864ConeFunctor L R a b γ).obj x) := rfl
    have h2 : (S1836IsoCommaNatIso L R).hom.app
        ((S1864ConeFunctor L R a b γ).obj x) =
        ((S1864ConeFunctor L R a b γ).obj x).obj.hom := rfl
    have h3 : ((S1864ConeFunctor L R a b γ).obj x).obj.hom =
        (γ.app x).hom := S1864ConeFunctor_obj_hom L R a b γ x
    have h4 : (γ.app x).hom = γ.hom.app x := Iso.app_hom γ x
    exact h1.trans (h2.trans (h3.trans h4))
  exact congrArg (fun γ' => (⟨a, b, γ'⟩ : S1893Cone L R X)) hγ

noncomputable def S1893ComparisonFunctor_obj_lift_iso (c : S1893Cone L R X) :
    Iso ((S1893ComparisonFunctor L R X).obj
      (S1864ConeFunctor L R c.toA c.toB c.commutes)) c :=
  eqToIso (S1893ComparisonFunctor_obj_lift_eq L R c)


instance S1893ComparisonFunctor_essSurj (X : Type u) [Category.{u, u} X] :
    (S1893ComparisonFunctor L R X).EssSurj where
  mem_essImage c :=
    ⟨S1864ConeFunctor L R c.toA c.toB c.commutes,
      ⟨S1893ComparisonFunctor_obj_lift_iso L R c⟩⟩

instance S1893ComparisonFunctor_isEquivalence (X : Type u) [Category.{u, u} X] :
    (S1893ComparisonFunctor L R X).IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

noncomputable def S1893ComparisonEquivalence (X : Type u) [Category.{u, u} X] :
    (X ⥤ S1836IsoComma L R) ≌ S1893Cone L R X :=
  (S1893ComparisonFunctor L R X).asEquivalence

noncomputable def S1893LiftUniq {c : S1893Cone L R X}
    {F : X ⥤ S1836IsoComma L R}
    (e : Iso ((S1893ComparisonFunctor L R X).obj F) c) :
    Iso F (S1893Lift L R c) :=
  Functor.FullyFaithful.preimageIso
    (Functor.FullyFaithful.ofFullyFaithful (S1893ComparisonFunctor L R X))
    (e.trans (S1893ComparisonFunctor_obj_lift_iso L R c).symm)

noncomputable def S1893LiftConeIso (F : X ⥤ S1836IsoComma L R) :
    Iso F (S1893Lift L R ((S1893ComparisonFunctor L R X).obj F)) :=
  S1893LiftUniq L R (Iso.refl ((S1893ComparisonFunctor L R X).obj F))

noncomputable def S1893LiftIsoOfConeIso {c : S1893Cone L R X}
    {F : X ⥤ S1836IsoComma L R}
    (e : Iso ((S1893ComparisonFunctor L R X).obj F) c) :
    Iso (S1893Lift L R c) F :=
  (S1893LiftUniq L R e).symm

theorem S1893CanonicalComparison_isEquivalence_of_coneIso
    {c : S1893Cone L R X} (F : X ⥤ S1836IsoComma L R) [F.IsEquivalence]
    (e : Iso ((S1893ComparisonFunctor L R X).obj F) c) :
    (S1893Lift L R c).IsEquivalence :=
  Functor.isEquivalence_of_iso (S1893LiftIsoOfConeIso L R e).symm

noncomputable def S1893UniversalCone :
    S1893Cone L R (S1836IsoComma L R) :=
  (S1893ComparisonFunctor L R (S1836IsoComma L R)).obj (𝟭 (S1836IsoComma L R))

noncomputable def S1893UniversalConeComparisonIso :
    Iso (S1893Lift L R (S1893UniversalCone L R)) (𝟭 (S1836IsoComma L R)) :=
  (S1893LiftConeIso L R (𝟭 (S1836IsoComma L R))).symm

theorem S1893UniversalConeComparison_isEquivalence :
    (S1893Lift L R (S1893UniversalCone L R)).IsEquivalence :=
  Functor.isEquivalence_of_iso (S1893UniversalConeComparisonIso L R).symm

end Basic

#check S1893ComparisonFunctor_isEquivalence
#check S1893ComparisonFunctor_obj_lift_iso
#check S1893LiftUniq
#check S1893CanonicalComparison_isEquivalence_of_coneIso
#check S1893UniversalConeComparison_isEquivalence

#print axioms S1893ComparisonFunctor_faithful
#print axioms S1893ComparisonFunctor_full
#print axioms S1893ComparisonFunctor_essSurj
#print axioms S1893ComparisonFunctor_isEquivalence
#print axioms S1893Lift_structure
#print axioms S1893ComparisonFunctor_obj_lift_iso
#print axioms S1893LiftUniq
#print axioms S1893CanonicalComparison_isEquivalence_of_coneIso
#print axioms S1893UniversalConeComparison_isEquivalence

end LeanFormal.IUT.XiFPaper.S1893PullbackUniversalActual
