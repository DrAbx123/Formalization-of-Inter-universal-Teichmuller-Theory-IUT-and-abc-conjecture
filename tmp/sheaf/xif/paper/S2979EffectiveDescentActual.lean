/-
S2979 -- effective descent for the A6 pointwise quotient (deep-audit group A).

Target: S2893A6QEffectiveDescent, equivalently S2882A6Q.IsStack etaleTopology.
This file is the first-error attack.  It does NOT claim the target.

## What is actually proved here

The A6 pointwise quotient is
  S2882A6Q.obj U = ActionCategory SignGroup (U -> X),
with SignGroup = Multiplicative (ZMod 2), X = S2844X, and the sign action
P |-> P ; S2882A6Aut g.  A descent datum D over a covering sieve R consists of
morphisms x_i : Y_i -> X together with twists (group elements)
  g(q,i1,i2,f1,f2) = twistVal (D.hom q f1 f2 hf1 hf2)
satisfying the cocycle conditions of Mathlib's Pseudofunctor.DescentData.

The file proves, with no sorry/axiom/placeholder:

* twistVal / objBack: the two projections of a morphism and of an object of a
  fiber (the group element and the underlying site-morphism), and their
  functoriality under QA6.map, including twistVal_comp (composition multiplies
  twists) and twistVal_map (pullback preserves twists).
* hom_twist_eq: the defining equation of a descent datum in this model,
    (f1 ; x_i1) ; S2882A6Aut g = f2 ; x_i2,
  where g is the twist of the descent hom at (q,f1,f2).  Equivalently: the
  underlying family of a descent datum is compatible precisely up to the
  twists, and the untwisted equality needed by Presieve.FamilyOfElements is
  exactly the twist-trivialization.  This is the key reduction.
* descentFamily and descentFamily_compatible_of_twist_one: the exact S2812
  gluing step for this quotient.  The family underlying a descent datum is
  compatible as soon as all its twists are trivial; hence effective descent
  for the quotient is equivalent to trivializing the twists of every datum.
* twist_conj_of_iso: if D lies in the essential image of toDescentData via x
  and an isomorphism e, then every self-twist of D (i.e. i1 = i2, so that the
  comparison morphism of e is the same at both ends) equals the canonical
  twist of toDescentData x, conjugated by the twist of the comparison:
    twistVal (D.hom q f1 f2) = h * twistVal (toDD x).hom q f1 f2 * h^-1.
  This requires the single-index (self-twist) form; the naive two-index form
  is false because the comparison twists at i1 and i2 differ.
* S2979CanonicalTwistTrivial: the canonical twist of toDescentData is 1.
  This is the first technical missing lemma; see the exact first error below.
* S2979NontrivialSelfTwist: the geometric obstruction datum (a covering sieve
  with a self-twist whose descent twist is nontrivial, i.e. a nontrivial etale
  SignGroup-torsor with an equivariant point).
* not_effective_of_nontrivial_selfTwist, not_target_of_twist and
  not_isStack_of_twist: canonical twist triviality plus a nontrivial self-twist
  refutes S2893A6QEffectiveDescent and S2893A6QIsStack.

## Exact first Lean error found

The S2812-style proof of effective descent has to show that the underlying
family of a descent datum is compatible.  In S2812 this is
descentFamily_compatible, proved because the fiber is discrete.  Here the
datum only gives the twisted equality hom_twist_eq, and the untwisted equality
is exactly the twist-trivialization, so the literal failing goal is

  (f1 ; objBack (D.obj i1)) ; S2882A6Aut (twistVal (D.hom ...)) = f2 ; objBack (D.obj i2)

with twistVal (D.hom ...) a nontrivial SignGroup element; no lemma in the
current tree identifies it with 1.  No source file constructs a descent datum
with a nontrivial twist either, so the failure is at the level of the missing
geometric input, not of a missing algebraic lemma.

The second, technical failure is S2979CanonicalTwistTrivial.  Unfolding
Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj and
Pseudofunctor.mapComp' reduces the goal to a product of twists of four
equality transports (two mapComp' components).  Lean's simp then fails with

  "The target expression is not type-correct under the instances
   transparency level"
  Application type mismatch: the argument Y has type
  @Iut.SchemeOverField S2847A6.F ... but is expected to have type
  @Iut.SchemeOverField K ...

because S2882A6Q is stated over K = S2844D6F6BaseChangeActual.K with the local
Field K instance of S2882, while S2893's statement is over S2847A6.F.  The two
are definitionally equal at default transparency, which is why S2893 compiles,
but not at the instances transparency used by the strict-coherence simp.

## The exact missing object

The missing object is a nontrivial etale SignGroup-torsor with an equivariant
point: a covering sieve R with a self-twist (i1 = i2 = i, f1 != f2,
f1 ; f_i = f2 ; f_i) whose descent twist is the nontrivial element of
SignGroup.  Such a datum exists as soon as the site has a nonsplit connected
etale Z/2-cover and a point fixed by S2882A6Aut: for instance a quadratic etale
cover of Spec F, or the [2]-cover of the A6 elliptic curve with a rational
2-torsion translation (the A6 curve has rational 2-torsion, S2826).  No such
cover/descent datum is constructed in this tree, and S1971/S2993 record the
same obstruction.  Consequently the target is expected to be FALSE, and the
correct object is the stackification/quotient stack (deep-audit group B); the
positive content here is that the obstruction is exactly a nontrivial twist.
-/
import tmp.sheaf.xif.paper.S2893A6QIsStackActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open Iut

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual

open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual

/-- The A6 base field, presented exactly as in S2882. -/
abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance instFieldK : Field K := S2847A6.fieldF

/-- The A6 pointwise quotient pseudofunctor. -/
abbrev QA6 : Iut.EtaleStackPseudofunctor K := S2882A6Q

/-- The target: effective descent for the A6 pointwise quotient. -/
abbrev Target : Prop := S2893A6QEffectiveDescent

/-! ## 1. The two projections of a fiber object and a fiber morphism -/

/-- The group element (twist) of a morphism between objects of a fiber. -/
abbrev twistVal {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    {P Q : QA6.obj U} (phi : P ⟶ Q) : Iut.SignGroup := phi.val

/-- The underlying site-morphism of an object of a fiber. -/
abbrev objBack {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (P : QA6.obj U) : Opposite.unop U.as ⟶ X := P.back

/-- Pullback of a fiber object is precomposition of the underlying morphism
(the .back form used in rewriting). -/
lemma back_map {U V : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (g : U ⟶ V) (P : QA6.obj U) :
    ((QA6.map g).toFunctor.obj P).back = g.as.unop ≫ P.back := rfl

/-- Pullback of a fiber object is precomposition of the underlying morphism. -/
lemma objBack_map {U V : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (g : U ⟶ V) (P : QA6.obj U) :
    objBack ((QA6.map g).toFunctor.obj P) = g.as.unop ≫ objBack P :=
  back_map g P

/-- The action is postcomposition with the sign automorphism. -/
lemma smul_eq_comp {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (P : Opposite.unop U.as ⟶ X) (g : Iut.SignGroup) :
    g • P = P ≫ S2882A6Aut g := rfl

/-- Composition of fiber morphisms multiplies twists. -/
lemma twistVal_comp {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    {P Q S' : QA6.obj U} (phi : P ⟶ Q) (psi : Q ⟶ S') :
    twistVal (phi ≫ psi) = twistVal psi * twistVal phi := rfl

/-- Pullback along a site morphism preserves the twist. -/
lemma twistVal_map {U V : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (g : U ⟶ V) {P Q : QA6.obj U} (phi : P ⟶ Q) :
    twistVal ((QA6.map g).toFunctor.map phi) = twistVal phi := rfl

/-! ## 2. The defining twist equation of a descent datum -/

/-- The twist equation: the local objects of a descent datum agree up to the
sign automorphism with the twist of the descent hom. -/
lemma hom_twist_eq {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (R : Sieve (Opposite.unop U.as))
    (D : QA6.DescentData (fun i : R.arrows.category => i.obj.hom))
    {Y : Iut.SchemeOverField K} (q : Y ⟶ Opposite.unop U.as)
    {i1 i2 : R.arrows.category} (f1 : Y ⟶ i1.obj.left) (f2 : Y ⟶ i2.obj.left)
    (hf1 : f1 ≫ i1.obj.hom = q) (hf2 : f2 ≫ i2.obj.hom = q) :
    (f1 ≫ objBack (D.obj i1)) ≫ S2882A6Aut (twistVal (D.hom q f1 f2 hf1 hf2))
      = f2 ≫ objBack (D.obj i2) := by
  -- The property of the Elements morphism is already the twisted equality;
  -- all remaining differences are definitional (actionAsFunctor.obj, the
  -- back projection of ActionCategory, and the sign action on points).
  exact (D.hom q f1 f2 hf1 hf2).property

/-! ## 3. The S2812 gluing step and the twist trivialization -/

/-- The underlying family of site-morphisms of a descent datum. -/
noncomputable def descentFamily {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (R : Sieve (Opposite.unop U.as))
    (D : QA6.DescentData (fun i : R.arrows.category => i.obj.hom)) :
    Presieve.FamilyOfElements (yoneda.obj X) R.arrows :=
  fun {Y} f hf => objBack (D.obj ⟨Over.mk f, hf⟩)

/-- If all twists of a descent datum are trivial, its underlying family is
compatible.  This is exactly S2812's descentFamily_compatible, and it shows
that the whole obstruction to effective descent is the twist. -/
lemma descentFamily_compatible_of_twist_one
    {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (R : Sieve (Opposite.unop U.as))
    (D : QA6.DescentData (fun i : R.arrows.category => i.obj.hom))
    (h : forall {Y : Iut.SchemeOverField K} (q : Y ⟶ Opposite.unop U.as)
      {i1 i2 : R.arrows.category} (f1 : Y ⟶ i1.obj.left) (f2 : Y ⟶ i2.obj.left)
      (hf1 : f1 ≫ i1.obj.hom = q) (hf2 : f2 ≫ i2.obj.hom = q),
      twistVal (D.hom q f1 f2 hf1 hf2) = 1) :
    (descentFamily R D).Compatible := by
  intro Y1 Y2 Z g1 g2 f1 f2 h1 h2 comm
  change g1 ≫ objBack (D.obj ⟨Over.mk f1, h1⟩) =
    g2 ≫ objBack (D.obj ⟨Over.mk f2, h2⟩)
  have htw := hom_twist_eq (R := R) (D := D) (q := g1 ≫ f1)
    (i1 := (⟨Over.mk f1, h1⟩ : R.arrows.category))
    (i2 := (⟨Over.mk f2, h2⟩ : R.arrows.category))
    (f1 := g1) (f2 := g2) rfl comm.symm
  rw [h (q := g1 ≫ f1)
    (i1 := (⟨Over.mk f1, h1⟩ : R.arrows.category))
    (i2 := (⟨Over.mk f2, h2⟩ : R.arrows.category))
    (f1 := g1) (f2 := g2) rfl comm.symm] at htw
  rw [S2882A6Aut_one, Category.comp_id] at htw
  exact htw

/-! ## 4. Twists of an effective descent datum (self-twist case) -/

/-- A self-twist of an effective descent datum equals the canonical twist of
toDescentData, conjugated by the twist of the comparison morphism.  The
single-index hypothesis is essential: for i1 != i2 the comparison twists at
the two ends differ and no such relation holds. -/
lemma twist_conj_of_iso
    {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (R : Sieve (Opposite.unop U.as))
    (D : QA6.DescentData (fun i : R.arrows.category => i.obj.hom))
    (x : QA6.obj U)
    (e : (QA6.toDescentData (fun i : R.arrows.category => i.obj.hom)).obj x ≅ D)
    {Y : Iut.SchemeOverField K} (q : Y ⟶ Opposite.unop U.as)
    (i : R.arrows.category) (f1 f2 : Y ⟶ i.obj.left)
    (hf1 : f1 ≫ i.obj.hom = q) (hf2 : f2 ≫ i.obj.hom = q) :
    twistVal (D.hom q f1 f2 hf1 hf2) =
      twistVal (e.hom.hom i) *
        twistVal (((QA6.toDescentData (fun i : R.arrows.category => i.obj.hom)).obj x).hom
          q f1 f2 hf1 hf2) * (twistVal (e.hom.hom i))⁻¹ := by
  have hcomm := e.hom.comm q f1 f2 hf1 hf2
  have hval := congrArg twistVal hcomm
  simp only [twistVal_comp, twistVal_map] at hval
  calc twistVal (D.hom q f1 f2 hf1 hf2)
      = (twistVal (D.hom q f1 f2 hf1 hf2) * twistVal (e.hom.hom i)) *
          (twistVal (e.hom.hom i))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = (twistVal (e.hom.hom i) *
          twistVal (((QA6.toDescentData (fun i : R.arrows.category => i.obj.hom)).obj x).hom
            q f1 f2 hf1 hf2)) * (twistVal (e.hom.hom i))⁻¹ := by
        rw [hval]

/-! ## 5. The first missing lemma and the geometric obstruction -/

/-- The canonical twist of toDescentData is trivial.  This is the first
missing lemma of the formalization: it is expected to be true (the strict
coherence of S2882A6Q is an equality transport), but the unfolding of
Pseudofunctor.DescentData.ofObj / Pseudofunctor.mapComp' currently breaks at
Lean's instances transparency; see the file header for the exact error. -/
def S2979CanonicalTwistTrivial : Prop :=
  forall {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (R : Sieve (Opposite.unop U.as)) (x : QA6.obj U)
    {Y : Iut.SchemeOverField K} (q : Y ⟶ Opposite.unop U.as)
    {i1 i2 : R.arrows.category} (f1 : Y ⟶ i1.obj.left) (f2 : Y ⟶ i2.obj.left)
    (hf1 : f1 ≫ i1.obj.hom = q) (hf2 : f2 ≫ i2.obj.hom = q),
    twistVal (((QA6.toDescentData (fun i : R.arrows.category => i.obj.hom)).obj x).hom
      q f1 f2 hf1 hf2) = 1

/-- The geometric obstruction datum: a covering sieve with a self-twist of a
descent datum whose twist is nontrivial.  Equivalently, a nontrivial etale
SignGroup-torsor with an equivariant point. -/
def S2979NontrivialSelfTwist : Prop :=
  exists (U : Iut.SchemeOverField K) (R : Sieve U),
    exists (_hR : R ∈ Iut.SchemeOverField.etaleTopology K U),
    exists (D : QA6.DescentData (fun i : R.arrows.category => i.obj.hom)),
    exists (i : R.arrows.category) (Y : Iut.SchemeOverField K) (q : Y ⟶ U),
    exists (f1 f2 : Y ⟶ i.obj.left),
    exists (hf1 : f1 ≫ i.obj.hom = q) (hf2 : f2 ≫ i.obj.hom = q),
    twistVal (D.hom q f1 f2 hf1 hf2) ≠ 1

/-- With canonical twist triviality, a nontrivial self-twist is not in the
essential image of toDescentData. -/
theorem not_effective_of_nontrivial_selfTwist
    (hcanon : S2979CanonicalTwistTrivial)
    {U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    (R : Sieve (Opposite.unop U.as))
    (D : QA6.DescentData (fun i : R.arrows.category => i.obj.hom))
    (i : R.arrows.category) {Y : Iut.SchemeOverField K}
    (q : Y ⟶ Opposite.unop U.as) (f1 f2 : Y ⟶ i.obj.left)
    (hf1 : f1 ≫ i.obj.hom = q) (hf2 : f2 ≫ i.obj.hom = q)
    (hg : twistVal (D.hom q f1 f2 hf1 hf2) ≠ 1) :
    Not (exists x : QA6.obj U,
      Nonempty ((QA6.toDescentData (fun i : R.arrows.category => i.obj.hom)).obj x ≅ D)) := by
  rintro ⟨x, ⟨e⟩⟩
  have he := twist_conj_of_iso R D x e q i f1 f2 hf1 hf2
  have ht := hcanon R x q f1 f2 hf1 hf2
  rw [he, ht] at hg
  exact hg (by rw [mul_one, mul_inv_cancel])

/-- Canonical twist triviality plus a nontrivial self-twist refutes the target. -/
theorem not_target_of_twist
    (hcanon : S2979CanonicalTwistTrivial) (H : S2979NontrivialSelfTwist) :
    Not Target := by
  obtain ⟨U, R, hR, D, i, Y, q, f1, f2, hf1, hf2, hg⟩ := H
  intro hT
  exact not_effective_of_nontrivial_selfTwist (U := LocallyDiscrete.mk (op U)) hcanon
    R D i q f1 f2 hf1 hf2 hg ((hT U R hR).mem_essImage D)

/-! ## 6. Consequence for the stack property -/

/-- Canonical twist triviality plus a nontrivial self-twist refutes the A6
stack statement itself. -/
theorem not_isStack_of_twist
    (hcanon : S2979CanonicalTwistTrivial) (H : S2979NontrivialSelfTwist) :
    Not S2893A6QIsStack := by
  intro hstack
  exact not_target_of_twist hcanon H (S2893A6QIsStack_iff_descent.mp hstack).2

/-! ## 7. Axiom audit -/

#print axioms back_map
#print axioms objBack_map
#print axioms smul_eq_comp
#print axioms twistVal_comp
#print axioms twistVal_map
#print axioms hom_twist_eq
#print axioms twist_conj_of_iso
#print axioms not_effective_of_nontrivial_selfTwist
#print axioms descentFamily_compatible_of_twist_one
#print axioms not_target_of_twist
#print axioms not_isStack_of_twist

end LeanFormal.IUT.XiFPaper.S2979EffectiveDescentActual
end
