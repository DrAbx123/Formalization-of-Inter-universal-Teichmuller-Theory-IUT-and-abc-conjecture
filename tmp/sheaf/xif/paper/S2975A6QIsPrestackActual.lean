/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S2899A6QPrestackActual
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# S2975: `S2882A6Q` is **not** an etale prestack

## Result

The exact target of task A1, `S2975A6QIsPrestack` =
`S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology F)`, is **false**.
This file proves

  `S2975A6QIsPrestack_false : ¬ S2975A6QIsPrestack`

with no `sorry` and no new axiom (axioms: `propext`, `Classical.choice`,
`Quot.sound`).

## Objectwise description of `Q.presheafHom` (the requested unfolding)

`S2882A6Q = S2882A6PFunctor.toPseudofunctor'` is the promotion of the strict
functor `S2882A6PFunctor : (SchemeOverField K)ᵒᵖ ⥤ Cat` whose value at `S` is the
action groupoid `ActionCategory SignGroup (S ⟶ X)` of the sign action on the
points of `X`, and whose action on morphisms is precomposition with the
pullback of test objects.  Consequently (see `S2975_presheafHom_obj` below),
for `T : Over S` the type of sections of `Q.presheafHom M N` at `T` is the
hom-type of action groupoids

  `(Q.map (T.hom.op).toLoc).toFunctor.obj M ⟶ (Q.map (T.hom.op).toLoc).toFunctor.obj N`

and, by `ActionCategory.hom_as_subtype`, a morphism between two such objects is a
sign element `g : SignGroup` with `g • a.back = b.back` (see
`S2975_action_hom_as_subtype`).  The remaining task of computing the restriction
maps of `presheafHom` (the `pullHom` 2-cell bookkeeping) is *not* the obstruction:
the statement itself is false.

## The obstruction

`IsPrestack` requires the sheaf condition for **every** covering sieve of every
test object, in particular for the empty sieve.  In the big etale topology the
empty sieve is covering for every point-free scheme: the jointly-surjective
component `jointlySurjectivePrecoverage` of the etale precoverage has no point
to cover, and `AlgebraicGeometry.Scheme.bot_mem_precoverage` supplies the rest.  Since
`GrothendieckTopology.over` transports this (Sieve.overEquiv preserves ⊥), the
empty sieve is covering in the slice site `Over S` at any `T` whose underlying
scheme `T.left` is the empty scheme.

For the empty family on the empty sieve the sheaf condition `∃! t, ...` is
vacuous except for uniqueness, so it forces `Subsingleton ((Q.presheafHom M N).obj T)`.
But at such a `T` the fibre of `Q` is the action groupoid of `SignGroup` on the
one-element type `(∅ ⟶ X)`; taking `M = N` the identity and the nontrivial sign
automorphism `Multiplicative.ofAdd 1` give two distinct sections whenever the
underlying point is fixed by the sign action (which it is, since `(∅ ⟶ X)` is a
subsingleton).  Hence the hom presheaf is not a sheaf for the empty cover.

## Consequence for the S2893/S2899/S2903/S2975 route

`S2893A6QIsStack`, `S2899A6QIsPrestack` (as an unconditional claim) and
`S2975A6QIsStackInhabitant` cannot be discharged for this `Q`: `IsStack`
extends `IsPrestack`, so it is refuted as well.  The missing object is not a
Mathlib computation lemma about `Functor.toPseudofunctor'` but a **correction of
the model**: a prestack/stack whose fibres are the pointwise action groupoid of
`Hom(S, X)` sees only the trivial sign-torsor; an honest quotient stack must
have as `S`-objects the sign-torsors over `S` equipped with a sign-equivariant
map to `X`.
-/

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper
open Iut
open scoped SpecOfNotation

namespace LeanFormal.IUT.XiFPaper.S2975A6QIsPrestackActual

open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open AlgebraicGeometry

abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF

/-! ## 0. The target statement and the objectwise description of the hom presheaf -/

/-- The target statement of task A1: `Q` is a prestack for the big etale topology. -/
def S2975A6QIsPrestack : Prop :=
  S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F)

/-- Objectwise description of `Q.presheafHom`: at `T : Over S` its sections are the
morphisms of the action groupoids obtained by pulling back along `T.hom`. -/
theorem S2975_presheafHom_obj (S : Iut.SchemeOverField K)
    (M N : S2882A6Q.obj (LocallyDiscrete.mk (Opposite.op S))) (T : (Over S)ᵒᵖ) :
    (S2882A6Q.presheafHom M N).obj T =
      ((S2882A6Q.map (unop T).hom.op.toLoc).toFunctor.obj M ⟶
        (S2882A6Q.map (unop T).hom.op.toLoc).toFunctor.obj N) :=
  Pseudofunctor.presheafHom_obj ..

/-- The hom-types in a fibre of `Q` are the sign elements moving one point to the other. -/
theorem S2975_action_hom_as_subtype {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (a b : S2882A6PointwiseQuotient U) :
    (a ⟶ b) = { g : SignGroup // g • a.back = b.back } :=
  ActionCategory.hom_as_subtype (M := SignGroup) (X := Opposite.unop U.as ⟶ X) a b

/-! ## 1. The empty sieve is a cover of a point-free test object -/

/-- For the big etale topology, the empty sieve covers every scheme with no points. -/
theorem S2975_bot_mem_etaleTopology_of_isEmpty {Z : AlgebraicGeometry.Scheme} [IsEmpty Z] :
    (⊥ : Sieve Z) ∈ AlgebraicGeometry.Scheme.etaleTopology Z := by
  change (⊥ : Sieve Z) ∈ (AlgebraicGeometry.Scheme.precoverage @Etale).toGrothendieck Z
  have h := Precoverage.generate_mem_toGrothendieck
    (AlgebraicGeometry.Scheme.bot_mem_precoverage (P := @Etale) Z)
  simpa using h

/-- The empty scheme, as an object of the site `Over (Spec K)`. -/
noncomputable def S2975EmptyObj : Iut.SchemeOverField K :=
  Over.mk (AlgebraicGeometry.Scheme.emptyTo (Spec(K)))

theorem S2975EmptyObj_left : S2975EmptyObj.left = (∅ : AlgebraicGeometry.Scheme) := rfl

instance S2975EmptyObj_isEmpty : IsEmpty S2975EmptyObj.left := by
  rw [S2975EmptyObj_left]
  infer_instance

/-- The empty sieve covers the empty test object of the site `Over (Spec K)`. -/
theorem S2975_bot_mem_etaleTopology_empty :
    (⊥ : Sieve S2975EmptyObj) ∈ Iut.SchemeOverField.etaleTopology K S2975EmptyObj := by
  change (⊥ : Sieve S2975EmptyObj) ∈
    GrothendieckTopology.over AlgebraicGeometry.Scheme.etaleTopology (Spec(K)) S2975EmptyObj
  rw [GrothendieckTopology.mem_over_iff,
    show Sieve.overEquiv S2975EmptyObj ⊥ = ⊥ from OrderIso.map_bot _]
  exact S2975_bot_mem_etaleTopology_of_isEmpty (Z := S2975EmptyObj.left)

/-! ## 2. The refutation

The sheaf condition is required for the empty sieve as well.  On a point-free
test object the empty sieve is a cover, so the sheaf condition forces the
hom-types in the fibre to be subsingletons.  But the fibre of `Q` at the empty
scheme is the action groupoid of `SignGroup` on the one-element type
`(∅ ⟶ X)`, so every object has the nontrivial sign automorphism; the hom-types
are not subsingletons. -/

open LeanFormal.IUT.XiFPaper.S1963SignActionAssemblyActual in
theorem S2975A6QIsPrestack_false : ¬ S2975A6QIsPrestack := by
  intro h
  -- the coefficient object in the fibre at `X`
  letI hFib : MulAction SignGroup (X ⟶ X) :=
    S2882A6PointMulAction (LocallyDiscrete.mk (Opposite.op X))
  let M : Cat.of (ActionCategory SignGroup (X ⟶ X)) :=
    ((𝟙 X : X ⟶ X) : ActionCategory SignGroup (X ⟶ X))
  -- the test object over `X` whose underlying scheme is empty
  let fY : S2975EmptyObj ⟶ X :=
    Over.homMk (AlgebraicGeometry.Scheme.emptyTo X.left) (AlgebraicGeometry.Scheme.empty_ext _ _)
  let T : Over X := Over.mk fY
  -- the empty sieve covers `T`
  have hbot : (⊥ : Sieve T) ∈ (Iut.SchemeOverField.etaleTopology K).over X T := by
    rw [GrothendieckTopology.mem_over_iff,
      show Sieve.overEquiv T (⊥ : Sieve T) = ⊥ from OrderIso.map_bot _]
    exact S2975_bot_mem_etaleTopology_empty
  -- the sheaf condition for the empty sieve
  have hS : Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over X)
      (S2882A6Q.presheafHom M M) := h.isSheaf M M
  have hfor : Presieve.IsSheafFor (S2882A6Q.presheafHom M M) ((⊥ : Sieve T) : Presieve T) :=
    Presheaf.IsSheaf.isSheafFor hS (⊥ : Sieve T) hbot
  have hfor' : Presieve.IsSheafFor (S2882A6Q.presheafHom M M) (⊥ : Presieve T) := by
    simpa using hfor
  -- hence all sections over `T` are subsingleton
  have hsub : Subsingleton ((S2882A6Q.presheafHom M M).obj (op T)) := by
    refine ⟨fun a b => ?_⟩
    have x : Presieve.FamilyOfElements (S2882A6Q.presheafHom M M) (⊥ : Presieve T) :=
      fun Y f hf => hf.elim
    have hx : x.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hsq
      exact h₁.elim
    obtain ⟨t, ht, huniq⟩ := hfor' x hx
    have ha : x.IsAmalgamation a := by intro Y f hf; exact hf.elim
    have hb : x.IsAmalgamation b := by intro Y f hf; exact hf.elim
    exact (huniq a ha).trans (huniq b hb).symm
  -- the fibre at `T.left`, and the pullback object
  letI hMA : MulAction SignGroup (T.left ⟶ X) :=
    S2882A6PointMulAction (LocallyDiscrete.mk (Opposite.op T.left))
  let A : ↑(S2882A6Q.obj (LocallyDiscrete.mk (Opposite.op T.left))) :=
    (S2882A6Q.map (T.hom.op.toLoc)).toFunctor.obj M
  have hobj : (S2882A6Q.presheafHom M M).obj (op T) = (A ⟶ A) := by
    rw [Pseudofunctor.presheafHom_obj]
    rfl
  -- the underlying scheme of `T` is empty, so hom-types out of it are subsingletons
  haveI hsingle : Subsingleton (T.left ⟶ X) := by
    refine ⟨fun f g => ?_⟩
    exact Over.OverMorphism.ext (AlgebraicGeometry.Scheme.empty_ext _ _)
  -- so the sign action fixes the underlying point
  have hfix : (Multiplicative.ofAdd (1 : ZMod 2)) • A.back = A.back := by
    show A.back ≫ S2882A6Aut (Multiplicative.ofAdd (1 : ZMod 2)) = A.back
    exact Subsingleton.elim _ _
  -- two distinct endomorphisms of `A`
  have hone : (1 : SignGroup) • A.back = A.back := by
    show A.back ≫ S2882A6Aut (1 : SignGroup) = A.back
    exact Subsingleton.elim _ _
  have hne : (⟨(1 : SignGroup), hone⟩ : A ⟶ A) ≠
      (⟨Multiplicative.ofAdd (1 : ZMod 2), hfix⟩ : A ⟶ A) := by
    intro hEq
    have hval := congrArg Subtype.val hEq
    have hval' : (1 : SignGroup) = Multiplicative.ofAdd (1 : ZMod 2) := hval
    exact S1963SignGroup_generator_ne hval'.symm
  have hneA : ¬ Subsingleton (A ⟶ A) := fun hss => hne (hss.elim _ _)
  exact hneA (hobj ▸ hsub)

/-! ## 3. Axiom footprint -/

#print axioms S2975_presheafHom_obj
#print axioms S2975_bot_mem_etaleTopology_empty
#print axioms S2975A6QIsPrestack_false

end LeanFormal.IUT.XiFPaper.S2975A6QIsPrestackActual
end