/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S2671
-/
import tmp.sheaf.xif.paper.S2667FiberCoherenceActual
import tmp.sheaf.xif.paper.S2662D9StackGoalReductionActual
import tmp.sheaf.xif.paper.S2666NewTorsorSheafActual
import tmp.sheaf.xif.paper.S2670D9EssSurjActual

/-!
# S2671: the non-empty freeness repair and the empty-object obstruction

## The repair

S2622TorsorData (the D9 hypothesis) is an empty type: its freeness field quantifies
over *all* test objects of the slice site, and the empty scheme forces 0 = 1 in
ZMod l.value (S2670TorsorData_false).  The natural repair is to ask for freeness
only on non-empty test objects.  This file introduces that repair as
S2671TorsorDataNonempty and proves that it is non-empty
(S2671TorsorDataNonempty_nonempty): the witness takes the empty scheme U = the empty
scheme with the trivial action, where the non-empty freeness hypothesis is vacuous.

## The obstruction

The repair cannot restore the D9 stack condition.  For **every** bare action-groupoid
datum D (in particular for every non-empty-only repair), the fiber pseudofunctor
S2667FiberPseudofunctor D is neither a prestack nor a stack for the full etale
topology on (SchemeOverField F).  The reason is the empty object of every slice
(Over S): the empty sieve is a cover of the empty object
(S2666EmptyObject_bot_mem), so any sheaf must take a subsingleton value there.
But at the empty object the hom presheaf of the action-groupoid fiber is the hom-set
of the action groupoid over (the empty scheme  \to  D.U), where all the elements
g : ZMod l.value give the same composite (every morphism out of the empty scheme is
unique), so its value contains at least the two distinct elements 0 and 1.  Hence
the sheaf condition for the empty sieve fails (S2671PresheafHom_not_isSheafFor_bot),
the D9 prestack goal fails (S2671Fiber_not_isPrestack), and the stack goal fails
(S2671Fiber_not_isStack).  This holds independently of any freeness hypothesis:
no restriction of freeness to non-empty test objects can make the *bare* action
groupoid a stack on the full site.  One must either remove the empty object from
the site or pass to the stackification.

## The honest conditional target

S2671FiberIsStack_of_input assembles a stack from the two actual inputs that the
geometric situation has to supply: the prestack condition and effectivity of
descent (essential surjectivity of toDescentData for every covering sieve).
It is statement-for-statement the D9 conditional target, with no extra hypothesis.
-/

noncomputable section
open CategoryTheory
open Opposite
open Iut
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2671D9StackRepairActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2662D9StackGoalReductionActual
open LeanFormal.IUT.XiFPaper.S2666NewTorsorSheafActual
open LeanFormal.IUT.XiFPaper.S2670D9EssSurjActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-! ## 1. The non-empty-only repair of the torsor datum -/

/-- Action-groupoid data with freeness required only on non-empty test objects.
This is the exact repair of S2622TorsorData suggested by the emptiness proof
S2670TorsorData_false: the empty scheme is excluded from the freeness quantifier. -/
structure S2671TorsorDataNonempty extends S2619ActionGroupoidData (l := l) (F := F) where
  hfree_nonempty :
    ∀ (V : (Iut.SchemeOverField F)ᵒᵖ), Nonempty V.unop.left →
      ∀ (M : V.unop ⟶ toS2619ActionGroupoidData.U) {g1 g2 : S2619G l},
        M ≫ (toS2619ActionGroupoidData.rho g1).hom =
          M ≫ (toS2619ActionGroupoidData.rho g2).hom → g1 = g2

namespace S2671TorsorDataNonempty

/-- The bare action-groupoid datum underlying a non-empty-only repaired datum. -/
abbrev toBare (D : S2671TorsorDataNonempty (l := l) (F := F)) :
    S2619ActionGroupoidData (l := l) (F := F) :=
  D.toS2619ActionGroupoidData

end S2671TorsorDataNonempty

/-- Every morphism of the slice site out of a *non-empty* object into the empty
scheme is impossible; equivalently the hom-type is a subsingleton. -/
theorem S2671OverHom_empty_subsingleton_of_nonempty
    (X : Iut.SchemeOverField F) (hX : Nonempty X.left) :
    Subsingleton (X ⟶ S2666EmptyBase (F := F)) := by
  refine ⟨fun f g => Over.OverMorphism.ext ?_⟩
  obtain ⟨x⟩ := hX
  haveI : IsEmpty (S2666EmptyBase (F := F)).left := by
    change IsEmpty (↥(∅ : AlgebraicGeometry.Scheme))
    infer_instance
  exact isEmptyElim (f.left x)

/-- The non-empty-only repaired torsor datum is non-empty: take the empty scheme
with the trivial action.  For a non-empty V there is no morphism (V  \to  the empty
scheme), so the freeness hypothesis is vacuous. -/
noncomputable def S2671TorsorDataNonempty_empty :
    S2671TorsorDataNonempty (l := l) (F := F) where
  U := S2666EmptyBase (F := F)
  rho := 1
  hfree_nonempty := by
    intro V hV M g1 g2 _
    obtain ⟨x⟩ := hV
    haveI : IsEmpty (S2666EmptyBase (F := F)).left := by
      change IsEmpty (↥(∅ : AlgebraicGeometry.Scheme))
      infer_instance
    exact isEmptyElim (M.left x)

theorem S2671TorsorDataNonempty_nonempty :
    Nonempty (S2671TorsorDataNonempty (l := l) (F := F)) :=
  ⟨S2671TorsorDataNonempty_empty (l := l) (F := F)⟩

/-! ## 2. The value of the hom presheaf at the empty object -/

/-- The action-groupoid object associated with a morphism m : S  \to  D.U. -/
noncomputable def S2671ActionObj
    (D : S2619ActionGroupoidData (l := l) (F := F))
    {S : Iut.SchemeOverField F} (m : S ⟶ D.U) :=
  letI : MulAction (S2619G l) (S2619Hom l F D (Opposite.op S)) :=
    S2619MulAction l F D (Opposite.op S)
  (⟨SingleObj.star (S2619G l), m⟩ :
    CategoryTheory.ActionCategory (S2619G l) (S2619Hom l F D (Opposite.op S)))

/-- The unique morphism of the slice site from the empty scheme to D.U. -/
noncomputable def S2671EmptyTo (D : S2619ActionGroupoidData (l := l) (F := F)) :
    S2666EmptyBase (F := F) ⟶ D.U :=
  Over.homMk (AlgebraicGeometry.Scheme.emptyTo D.U.left)
    (AlgebraicGeometry.Scheme.empty_ext _ _)

/-- Morphisms of the slice site out of the empty object of Over S into D.U form
a subsingleton: their underlying scheme morphisms start at the empty scheme. -/
theorem S2671EmptyObject_hom_subsingleton
    (D : S2619ActionGroupoidData (l := l) (F := F)) (S : Iut.SchemeOverField F) :
    Subsingleton ((S2666EmptyObject (F := F) S).left ⟶ D.U) :=
  ⟨fun f g => Over.OverMorphism.ext (AlgebraicGeometry.Scheme.empty_ext _ _)⟩

/-- The object part of the pullback functor along the empty object of Over S,
computed on the second component. -/
@[simp]
theorem S2671PullFunctor_obj_back
    (D : S2619ActionGroupoidData (l := l) (F := F))
    {V V' : (Iut.SchemeOverField F)ᵒᵖ} (h : V ⟶ V')
    (M : S2619FiberAt l F D V) :
    ((S2619PullFunctor l F D h).obj M).back = h.unop ≫ M.back := rfl

/-- **Computation of the hom presheaf at the empty object.** -/
theorem S2671PresheafHom_empty_obj_eq
    (D : S2619ActionGroupoidData (l := l) (F := F)) (S : Iut.SchemeOverField F)
    (M N : S2619FiberAt l F D (Opposite.op S)) :
    ((S2667FiberPseudofunctor l F D).presheafHom M N).obj
        (Opposite.op (S2666EmptyObject (F := F) S)) =
      ((S2619PullFunctor l F D (S2666EmptyObject (F := F) S).hom.op).obj M ⟶
        (S2619PullFunctor l F D (S2666EmptyObject (F := F) S).hom.op).obj N) :=
  rfl

/-- Endomorphisms of an object of an action groupoid contain the scalars 0 and 1
whenever the action identifies the source with the target for every scalar. -/
theorem S2671ActionHom_not_subsingleton {X : Type u} [MulAction (S2619G l) X]
    (p q : CategoryTheory.ActionCategory (S2619G l) X)
    (h : ∀ g : S2619G l, g • p.back = q.back) :
    ¬ Subsingleton (p ⟶ q) := by
  intro hs
  rw [CategoryTheory.ActionCategory.hom_as_subtype] at hs
  have h01 : (0 : S2619G l) = 1 := by
    have e : (⟨0, h 0⟩ : {m : S2619G l // m • p.back = q.back}) = ⟨1, h 1⟩ :=
      hs.elim _ _
    exact congrArg Subtype.val e
  exact S2670ZMod_zero_ne_one h01

/-- **The empty-object computation.**  At the empty object of the slice Over S, the
hom presheaf of the action-groupoid fiber is not a subsingleton: all morphisms out of
the empty scheme into D.U are equal, so every scalar g gives a morphism between
the two pulled-back objects, and 0 and 1 are different in ZMod l.value. -/
theorem S2671PresheafHom_empty_not_subsingleton
    (D : S2619ActionGroupoidData (l := l) (F := F)) (S : Iut.SchemeOverField F)
    (M N : S2619FiberAt l F D (Opposite.op S)) :
    ¬ Subsingleton
      (((S2667FiberPseudofunctor l F D).presheafHom M N).obj
        (Opposite.op (S2666EmptyObject (F := F) S))) := by
  rw [S2671PresheafHom_empty_obj_eq (D := D) (S := S) (M := M) (N := N)]
  letI : MulAction (S2619G l)
      (S2619Hom l F D (Opposite.op S)) :=
    S2619MulAction l F D (Opposite.op S)
  letI : MulAction (S2619G l)
      (S2619Hom l F D (Opposite.op (S2666EmptyObject (F := F) S).left)) :=
    S2619MulAction l F D (Opposite.op (S2666EmptyObject (F := F) S).left)
  refine S2671ActionHom_not_subsingleton
    (p := (S2619PullFunctor l F D (S2666EmptyObject (F := F) S).hom.op).obj M)
    (q := (S2619PullFunctor l F D (S2666EmptyObject (F := F) S).hom.op).obj N) ?_
  intro g
  rw [S2671PullFunctor_obj_back, S2671PullFunctor_obj_back]
  change ((S2666EmptyObject (F := F) S).hom ≫ M.back) ≫ (D.rho g).hom =
    (S2666EmptyObject (F := F) S).hom ≫ N.back
  haveI := S2671EmptyObject_hom_subsingleton (l := l) (F := F) D S
  exact Subsingleton.elim _ _

/-! ## 3. Failure of the sheaf condition at the empty covering sieve -/

/-- If a presheaf of types satisfies the sheaf condition for the empty sieve on X,
then its value at X is a subsingleton: the empty family is compatible and every
element is an amalgamation of it. -/
theorem S2671Subsingleton_of_isSheafFor_bot {C : Type*} [Category C]
    {P : Cᵒᵖ ⥤ Type} {X : C}
    (h : Presieve.IsSheafFor P (⊥ : Sieve X).arrows) :
    Subsingleton (P.obj (Opposite.op X)) := by
  refine ⟨fun t₁ t₂ => ?_⟩
  let x : Presieve.FamilyOfElements P (⊥ : Sieve X).arrows := fun _ _ hf => False.elim hf
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomp
    exact False.elim h₁
  obtain ⟨t, ht, huniq⟩ := h x hx
  exact (huniq t₁ (by intro Y f hf; exact False.elim hf)).trans
    (huniq t₂ (by intro Y f hf; exact False.elim hf)).symm

/-- **The empty covering sieve kills the hom presheaf.**  The empty sieve on the
empty object of Over S is a cover for the etale topology, but the value of the hom
presheaf there is not a subsingleton. -/
theorem S2671PresheafHom_not_isSheafFor_bot
    (D : S2619ActionGroupoidData (l := l) (F := F)) (S : Iut.SchemeOverField F)
    (M N : S2619FiberAt l F D (Opposite.op S)) :
    ¬ Presieve.IsSheafFor ((S2667FiberPseudofunctor l F D).presheafHom M N)
      (⊥ : Sieve (S2666EmptyObject (F := F) S)).arrows := by
  intro h
  exact S2671PresheafHom_empty_not_subsingleton (l := l) (F := F) D S M N
    (S2671Subsingleton_of_isSheafFor_bot h)

/-- **No bare action-groupoid fiber is a prestack on the full etale site.**  The
empty object of the slice over the empty scheme provides a covering sieve for which
the descent condition on morphisms fails, for every D. -/
theorem S2671Fiber_not_isPrestack
    (D : S2619ActionGroupoidData (l := l) (F := F)) :
    ¬ (S2667FiberPseudofunctor l F D).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) := by
  intro hpre
  haveI : MulAction (S2619G l)
      (S2619Hom l F D (Opposite.op (S2666EmptyBase (F := F)))) :=
    S2619MulAction l F D (Opposite.op (S2666EmptyBase (F := F)))
  have hsheaf : ∀ {S : Iut.SchemeOverField F}
      (M N : (S2667FiberPseudofunctor l F D).obj (LocallyDiscrete.mk (Opposite.op S))),
      Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
        ((S2667FiberPseudofunctor l F D).presheafHom M N) :=
    (S2662PrestackGoal_iff_isSheaf (F := F)
      (fib := S2667FiberPseudofunctor l F D)).mp hpre
  let m : S2666EmptyBase (F := F) ⟶ D.U := S2671EmptyTo (l := l) (F := F) D
  let M : S2619FiberAt l F D (Opposite.op (S2666EmptyBase (F := F))) :=
    S2671ActionObj (l := l) (F := F) D m
  have hIsSheaf : Presheaf.IsSheaf
      ((Iut.SchemeOverField.etaleTopology F).over (S2666EmptyBase (F := F)))
      ((S2667FiberPseudofunctor l F D).presheafHom M M) :=
    hsheaf M M
  exact S2671PresheafHom_not_isSheafFor_bot (l := l) (F := F) D
    (S2666EmptyBase (F := F)) M M
    ((isSheaf_iff_isSheaf_of_type _ _).mp hIsSheaf
      (⊥ : Sieve (S2666EmptyObject (F := F) (S2666EmptyBase (F := F))))
      (S2666EmptyObject_bot_mem (F := F) (S2666EmptyBase (F := F))))

/-- **No bare action-groupoid fiber is a stack on the full etale site.** -/
theorem S2671Fiber_not_isStack
    (D : S2619ActionGroupoidData (l := l) (F := F)) :
    ¬ (S2667FiberPseudofunctor l F D).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  fun h => S2671Fiber_not_isPrestack (l := l) (F := F) D h.toIsPrestack

/-- The non-empty-only repair does not help: the bare action-groupoid fiber of every
non-empty-only repaired datum still fails to be a prestack. -/
theorem S2671NonemptyRepair_not_isPrestack
    (D : S2671TorsorDataNonempty (l := l) (F := F)) :
    ¬ (S2667FiberPseudofunctor l F D.toBare).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) :=
  S2671Fiber_not_isPrestack (l := l) (F := F) D.toBare

/-- In particular the non-empty-only repair does not give a stack either. -/
theorem S2671NonemptyRepair_not_isStack
    (D : S2671TorsorDataNonempty (l := l) (F := F)) :
    ¬ (S2667FiberPseudofunctor l F D.toBare).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  fun h => S2671NonemptyRepair_not_isPrestack (l := l) (F := F) D h.toIsPrestack

/-! ## 4. The honest conditional D9 stack theorem -/

/-- **Conditional D9 target.**  The fiber pseudofunctor of a bare action-groupoid
datum is a stack as soon as the two actual descent inputs are supplied: the prestack
condition and effectivity of descent (essential surjectivity of the descent functor
for every covering sieve).  This is the honest, non-vacuous target: the
essSurj input is not derivable from freeness (and is false for the constant group
scheme with non-trivial torsors), and by S2671Fiber_not_isPrestack the prestack
input cannot hold on the full site at all. -/
theorem S2671FiberIsStack_of_input
    (D : S2619ActionGroupoidData (l := l) (F := F))
    (hpre : (S2667FiberPseudofunctor l F D).IsPrestack
      (Iut.SchemeOverField.etaleTopology F))
    (hess : ∀ {S : Iut.SchemeOverField F} (R : Sieve S),
      R ∈ Iut.SchemeOverField.etaleTopology F S →
      ((S2667FiberPseudofunctor l F D).toDescentData
        (fun (f : R.arrows.category) => f.obj.hom)).EssSurj) :
    (S2667FiberPseudofunctor l F D).IsStack
      (Iut.SchemeOverField.etaleTopology F) where
  toIsPrestack := hpre
  essSurj_of_sieve := fun R hR => hess R hR

#print axioms S2671TorsorDataNonempty_nonempty
#print axioms S2671ActionHom_not_subsingleton
#print axioms S2671PresheafHom_empty_not_subsingleton
#print axioms S2671PresheafHom_not_isSheafFor_bot
#print axioms S2671Fiber_not_isPrestack
#print axioms S2671Fiber_not_isStack
#print axioms S2671NonemptyRepair_not_isPrestack
#print axioms S2671NonemptyRepair_not_isStack
#print axioms S2671FiberIsStack_of_input

end LeanFormal.IUT.XiFPaper.S2671D9StackRepairActual
end
