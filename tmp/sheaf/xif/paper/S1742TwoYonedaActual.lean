import Iut.Foundations.Orbicurve

/-!
# S1742: the 2-Yoneda comparison for representable etale pseudofunctors

For a field `F` and schemes `S T : Over (Spec F)`, this file constructs both
directions of the comparison

`Pseudofunctor.StrongTrans (schemeRepresentableEtalePseudofunctor F S)
  (schemeRepresentableEtalePseudofunctor F T)`  (up to 2-isomorphism)
`<->`  `S ⟶ T`  (in `Over (Spec F)`),

and proves that they are mutually inverse: strictly on scheme morphisms and up
to a 2-isomorphism (an `Iso` in the category of strong transformations) on the
side of strong transformations.

## What is built

* `S1742App`: the `app` component of the strong transformation induced by a
  scheme morphism `f : S ⟶ T`, defined by postcomposition with `f`.
* `S1742Nat`: its strong naturality 2-isomorphism (a 2-isomorphism in `Cat`),
  built from `Category.assoc`; its coherence fields are subsingleton proofs
  because the target categories are discrete.
* `S1742StrongTransOfHom`: the actual `Pseudofunctor.StrongTrans`.
* `S1742HomOfStrongTrans`: the reverse direction, the underlying scheme
  morphism obtained as the image of `𝟙 S` under `eta.app` at `S`.
* `S1742HomOfStrongTrans_strongTransOfHom`: the round trip on scheme
  morphisms is the identity (`𝟙 S ≫ f = f`).
* `S1742Key`: every component of `eta.app` is determined by
  `S1742HomOfStrongTrans eta` (via the strong naturality constraint at `S`).
* `S1742AppEq` / `S1742StrongTransIsoOfHom`: the reverse round trip is an
  actual 2-isomorphism
  `S1742StrongTransOfHom (S1742HomOfStrongTrans eta) ≅ eta`.
* `S1742HomOfStrongTrans_congr`: the reverse direction is well defined on
  2-isomorphism classes, so the comparison is a bijection between scheme
  morphisms `S ⟶ T` and 2-isomorphism classes of strong transformations.
* `S1742TwoYoneda_comparison`: the packaged statement of both round trips.

No `sorry`, no new axiom, no `Shrink`, no `ULift` coercion of the data: the
target categories are Mathlib's `Discrete` categories of scheme morphisms, and
the coherence data are the actual structure fields of
`Pseudofunctor.StrongTrans`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

open CategoryTheory
open AlgebraicGeometry

variable {F : Type} [Field F]

/-- The representable category-valued etale pseudofunctor of `S`, abbreviated. -/
abbrev S1742YS (S : Iut.SchemeOverField F) : Iut.EtaleStackPseudofunctor F :=
  Iut.schemeRepresentableEtalePseudofunctor F S

variable {S T : Iut.SchemeOverField F}

/-! ## 0. Unfolding lemmas for the representable pseudofunctor -/

/-- The `1`-morphism component of the representable pseudofunctor on objects of the
site is the map of the representable fiber functor. -/
lemma S1742YS_map (S : Iut.SchemeOverField F)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (g : a ⟶ b) :
    (S1742YS (F := F) S).map g = (Iut.schemeRepresentableFiberFunctor F S).map g.as := rfl

/-- The representable fiber functor acts on objects by precomposition. -/
lemma S1742Fiber_map_obj (S : Iut.SchemeOverField F)
    {U V : (Iut.SchemeOverField F)ᵒᵖ} (φ : U ⟶ V) (P : Opposite.unop U ⟶ S) :
    ((Iut.schemeRepresentableFiberFunctor F S).map φ).toFunctor.obj (Discrete.mk P) =
      Discrete.mk (φ.unop ≫ P) := rfl

/-- Composition of `1`-morphisms in `Cat` is composition of functors. -/
lemma S1742Comp_toFunctor_obj {C D E : Cat} (G : C ⟶ D) (H : D ⟶ E) (X : C) :
    (G ≫ H).toFunctor.obj X = H.toFunctor.obj (G.toFunctor.obj X) := rfl

/-! ## 1. Forward direction: a scheme morphism gives a strong transformation -/

/-- The `app` component of the strong transformation induced by `f : S ⟶ T`:
at a test object `U` it postcomposes every section `U ⟶ S` with `f`. -/
noncomputable def S1742App (f : S ⟶ T)
    (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    (S1742YS (F := F) S).obj U ⟶ (S1742YS (F := F) T).obj U :=
  (Discrete.functor
    (fun P : Opposite.unop U.as ⟶ S => Discrete.mk (P ≫ f))).toCatHom

/-- The value of `S1742App` on an object of the discrete category. -/
lemma S1742App_obj (f : S ⟶ T) (U : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S) :
    (S1742App f U).toFunctor.obj (Discrete.mk P) = Discrete.mk (P ≫ f) := rfl

/-- The strong naturality 2-isomorphism of `S1742App`. -/
noncomputable def S1742Nat (f : S ⟶ T)
    {a b : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ} (g : a ⟶ b) :
    (S1742YS (F := F) S).map g ≫ S1742App f b ≅
      S1742App f a ≫ (S1742YS (F := F) T).map g := by
  apply eqToIso
  apply Cat.ext
  apply Discrete.functor_ext
  intro P
  rw [S1742Comp_toFunctor_obj, S1742Comp_toFunctor_obj, S1742YS_map, S1742YS_map,
    S1742Fiber_map_obj, S1742App_obj, S1742App_obj, S1742Fiber_map_obj]
  exact Discrete.ext (Category.assoc _ _ _)

/-- The actual strong transformation of representable pseudofunctors induced by a
scheme morphism `f : S ⟶ T`. -/
noncomputable def S1742StrongTransOfHom (f : S ⟶ T) :
    Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T) where
  app U := S1742App f U
  naturality g := S1742Nat f g
  naturality_naturality := by
    intro a b f' g' eta
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f' g'
    apply CategoryTheory.Cat.Hom₂.ext
    apply CategoryTheory.NatTrans.ext
    funext X
    apply ULift.ext
    exact Subsingleton.elim _ _

/-! ## 2. Reverse direction: a strong transformation gives a scheme morphism -/

/-- The underlying scheme morphism `S ⟶ T` of a strong transformation: the image
of the identity section `𝟙 S` under the `app` component at `S`. -/
noncomputable def S1742HomOfStrongTrans
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)) : S ⟶ T :=
  ((eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj (Discrete.mk (𝟙 S))).as

/-- The defining computation rule of `S1742HomOfStrongTrans`. -/
lemma S1742HomOfStrongTrans_def
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)) :
    ((eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj
        (Discrete.mk (𝟙 S))).as = S1742HomOfStrongTrans eta := rfl

/-! ## 3. The round trip on scheme morphisms is the identity -/

/-- Applying the reverse direction to the strong transformation of a scheme
morphism recovers that morphism. -/
theorem S1742HomOfStrongTrans_strongTransOfHom (f : S ⟶ T) :
    S1742HomOfStrongTrans (S1742StrongTransOfHom f) = f := by
  rw [← S1742HomOfStrongTrans_def (S1742StrongTransOfHom f)]
  show (Discrete.mk (𝟙 S ≫ f)).as = f
  exact Category.id_comp f

/-! ## 4. Strong naturality determines every component of a strong transformation -/

/-- Key computation: the value of `eta.app` at any test object and section is the
postcomposition of that section with the underlying scheme morphism of `eta`.
This is the strong naturality constraint of `eta` evaluated at the identity
section. -/
lemma S1742Key
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T))
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) (P : Opposite.unop a.as ⟶ S) :
    ((eta.app a).toFunctor.obj (Discrete.mk P)).as = P ≫ S1742HomOfStrongTrans eta := by
  have hζ : (eta.app (LocallyDiscrete.mk (Opposite.op S))).toFunctor.obj (Discrete.mk (𝟙 S))
      = Discrete.mk (S1742HomOfStrongTrans eta) := Discrete.mk_as _
  have h := Discrete.eq_of_hom
    (((eta.naturality
      (Discrete.mk (P.op) : (LocallyDiscrete.mk (Opposite.op S)) ⟶ a)).hom).toNatTrans.app
        (Discrete.mk (𝟙 S)))
  simp only [S1742Comp_toFunctor_obj] at h
  rw [hζ] at h
  simp only [S1742YS_map] at h
  exact h

/-- Every `app` component of a strong transformation agrees with the `app`
component of the strong transformation of its underlying scheme morphism. -/
lemma S1742AppEq
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T))
    (a : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ) :
    S1742App (S1742HomOfStrongTrans eta) a = eta.app a := by
  apply Cat.ext
  apply Discrete.functor_ext
  intro P
  exact Discrete.ext (S1742Key eta a P).symm

/-! ## 5. The round trip on strong transformations is a 2-isomorphism -/

/-- The reverse round trip: rebuilding the strong transformation from the underlying
scheme morphism recovers the original strong transformation up to 2-isomorphism. -/
noncomputable def S1742StrongTransIsoOfHom
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)) :
    S1742StrongTransOfHom (S1742HomOfStrongTrans eta) ≅ eta :=
  Pseudofunctor.StrongTrans.isoMk
    (fun a => eqToIso (S1742AppEq eta a))
    (by
      intro a b g
      apply CategoryTheory.Cat.Hom₂.ext
      apply CategoryTheory.NatTrans.ext
      funext X
      apply ULift.ext
      exact Subsingleton.elim _ _)

/-- The two directions are mutually inverse: the composite on strong
transformations is isomorphic to the identity, so the comparison is a bijection
on 2-isomorphism classes. -/
theorem S1742StrongTransIsoOfHom_nonempty
    (eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)) :
    Nonempty (S1742StrongTransOfHom (S1742HomOfStrongTrans eta) ≅ eta) :=
  ⟨S1742StrongTransIsoOfHom eta⟩

/-- The reverse direction is well defined on 2-isomorphism classes: isomorphic
strong transformations have the same underlying scheme morphism.  Together with
`S1742StrongTransIsoOfHom` this identifies scheme morphisms with 2-isomorphism
classes of strong transformations of representable pseudofunctors. -/
theorem S1742HomOfStrongTrans_congr
    {eta theta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T)}
    (e : eta ≅ theta) :
    S1742HomOfStrongTrans eta = S1742HomOfStrongTrans theta :=
  Discrete.eq_of_hom
    ((e.hom.as.app (LocallyDiscrete.mk (Opposite.op S))).toNatTrans.app (Discrete.mk (𝟙 S)))

/-- The 2-Yoneda comparison, packaged: the two constructions are inverse
(strictly in one direction, up to 2-isomorphism in the other). -/
theorem S1742TwoYoneda_comparison :
    (∀ f : S ⟶ T, S1742HomOfStrongTrans (S1742StrongTransOfHom f) = f) ∧
      (∀ eta : Pseudofunctor.StrongTrans (S1742YS (F := F) S) (S1742YS (F := F) T),
        Nonempty (S1742StrongTransOfHom (S1742HomOfStrongTrans eta) ≅ eta)) :=
  ⟨S1742HomOfStrongTrans_strongTransOfHom,
    S1742StrongTransIsoOfHom_nonempty⟩

/-! ## 6. Target-locked type checks

The two constructions have exactly the type of the S1733 2-Yoneda comparison,
with the representable pseudofunctors written out. -/

example :
    (S ⟶ T) →
      Pseudofunctor.StrongTrans (Iut.schemeRepresentableEtalePseudofunctor F S)
        (Iut.schemeRepresentableEtalePseudofunctor F T) :=
  S1742StrongTransOfHom

example :
    Pseudofunctor.StrongTrans (Iut.schemeRepresentableEtalePseudofunctor F S)
        (Iut.schemeRepresentableEtalePseudofunctor F T) → (S ⟶ T) :=
  S1742HomOfStrongTrans

#check @S1742StrongTransOfHom
#check @S1742HomOfStrongTrans
#check @S1742HomOfStrongTrans_strongTransOfHom
#check @S1742StrongTransIsoOfHom
#check @S1742HomOfStrongTrans_congr
#check @S1742TwoYoneda_comparison

end LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual


