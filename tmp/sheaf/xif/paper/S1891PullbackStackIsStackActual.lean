/-
# S1891: IsStack for the iso-comma (two-fibre-product) pseudofunctor

## Question

S1864 isolated the exact missing item (b) of the two-pullback obligation: the
effective-descent statement `IsStack` for the category-valued pseudofunctor on
the étale site whose value at a test object `U` is the iso-comma category of
the two cover maps at `U`.  The task is to prove that `IsStack` given the
pseudofunctor of S1890 (or, since the S1890 file is not present in the
workspace, given its interface), or else to isolate the exact first missing
statement.

This file answers the second alternative.  **No `IsStack` proof is faked.**

## What Mathlib has, and what it does not have

Mathlib has the effective-descent predicate for category-valued
pseudofunctors on a site (`CategoryTheory.Pseudofunctor.IsStack`, in
`Mathlib.CategoryTheory.Sites.Descent.IsStack`), the descent-data category
(`Pseudofunctor.DescentData`), the prestacks
(`Pseudofunctor.IsPrestack`, `IsPrestackFor`), and the constructor
`Pseudofunctor.IsStack.of_isStackFor` which reduces stackhood to the
descent-data functors being equivalences for every covering sieve (see the
`#check` block in Section 6).

Mathlib also has `Comma.map` and the *one-sided* comparisons
`Comma.mapLeftId`, `Comma.mapLeftComp`, `Comma.mapLeftEq`
(`Mathlib/CategoryTheory/Comma/Basic.lean`).  It does **not** have:

* a comparison isomorphism for a composite of two two-sided `Comma.map`
  functors, hence no pseudofunctor whose values are the comma categories;
* any statement about the behaviour of `Pseudofunctor.DescentData` or
  `Pseudofunctor.IsStack` under a pointwise (two-sided) iso-comma, product or
  two-fibre product of pseudofunctors;
* any instance of `IsStack` for a pointwise two-limit of stacks.

The exact first missing mathematical statement is therefore:

  **the pointwise two-fibre product (iso-comma) of three stacks is a stack.**

The file states this precisely (Section 1), shows that it is exactly the
missing ingredient for the stack half of S1864's obligation (Section 2), and
proves the unconditional parts that are available: the reduction from
S1864's first missing statement (Section 2), the identity-leg cases, both at
the actual site (Section 3) and at an arbitrary site (Section 4), the case in
which one leg is a pointwise equivalence of categories (Section 5), and the
equivalence between the existence form and the interface form (Section 6).
These cases are genuine inhabitants of the missing `Prop`: the missing
theorem is non-vacuous, and the general cospan is exactly what remains open.

## Honest boundary

No `sorry`, no `axiom`, no `Shrink`, `ULift` or `PUnit`, and no fake stack.
`S1891StackTwoFiberProductDescent` is a named `Prop` with no inhabitant
asserted.  The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`; see the `#print axioms` block.
-/

import tmp.sheaf.xif.paper.S1864GeneralPullbackStackActual
import Mathlib.CategoryTheory.Sites.Descent.IsStack

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1836CoverPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual

universe u

/-! ## 1. The exact missing statement: the two-fibre product of stacks -/

/-- **The two-fibre-product stack, existence form.**  For a cospan of
category-valued pseudofunctors `L : F ⟶ H`, `R : G ⟶ H` on a site `(C, J)`,
this says that there is a pseudofunctor `P` whose value at every test object
`U` is equivalent to the iso-comma category of `L.app U` and `R.app U`, and
which is a stack for `J`.  This is the pointwise two-fibre product of
stacks. -/
def S1891IsoCommaStackExistsFor
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H) : Prop :=
  ∃ P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u},
    P.IsStack J ∧
      ∀ U : LocallyDiscrete Cᵒᵖ,
        Nonempty (↑(P.obj U) ≌
          S1836IsoComma (L.app U).toFunctor (R.app U).toFunctor)

/-- **The exact first missing descent theorem.**  For every site and every
cospan of three stacks, there is a pseudofunctor with iso-comma values which
is a stack.  This is the statement "a two-fibre product of stacks is a
stack", in the form needed by S1864; it is not present in Mathlib. -/
def S1891StackTwoFiberProductDescent : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H),
    F.IsStack J → G.IsStack J → H.IsStack J →
    S1891IsoCommaStackExistsFor J F G H L R

/-- **S1890's pseudofunctor interface.**  The output of S1890 is a
pseudofunctor `P` on the site together with equivalences between its values
and the iso-comma categories of the two legs.  This is exactly the interface
needed to state `IsStack` for the iso-comma pseudofunctor. -/
structure S1891IsoCommaPseudofunctor
    {C : Type (u + 1)} [Category.{u} C]
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H) where
  /-- the pseudofunctor constructed by S1890 -/
  P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u}
  /-- its values are the iso-comma categories -/
  fiberEquiv : ∀ U : LocallyDiscrete Cᵒᵖ,
    ↑(P.obj U) ≌ S1836IsoComma (L.app U).toFunctor (R.app U).toFunctor

/-- **The missing statement is exactly the existence of an interface whose
pseudofunctor is a stack.**  This is the interface form of the missing
descent theorem. -/
theorem S1891IsoCommaStackExistsFor_iff_interface
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H) :
    S1891IsoCommaStackExistsFor J F G H L R ↔
      ∃ I : S1891IsoCommaPseudofunctor F G H L R, I.P.IsStack J := by
  constructor
  · rintro ⟨P, hP, e⟩
    exact ⟨⟨P, fun U => (e U).some⟩, hP⟩
  · rintro ⟨I, hI⟩
    exact ⟨I.P, hI, fun U => ⟨I.fiberEquiv U⟩⟩

/-! ## 2. The actual étale site of the S1726 orbicurve -/

/-- **The stack half of S1864's obligation at the actual site.**  For every
cospan of actual finite-étale cover maps `f : A ⟶ C`, `g : B ⟶ C`, there is
an actual étale stack over `S1726K` whose fibre at every test object `U` is
equivalent to the iso-comma category of the two maps at `U`.  This is
exactly the `stack` and `fiberEquiv` fields of
`S1864IsoCommaStackObligation`; the remaining fields (projections, structure
map, universal property) are not part of the descent statement. -/
def S1891IsoCommaStackCore {A B C : S1728Cover}
    (f : S1728CoverMap A C) (g : S1728CoverMap B C) : Prop :=
  ∃ stack : EtaleStackOverField S1726K,
    ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
      Nonempty (↑(stack.fiber.obj U) ≌
        S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor)

/-- The core statement is the stackhood of an iso-comma pseudofunctor, with
the fibre equivalences exposed. -/
theorem S1891IsoCommaStackCore.isStack {A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (h : S1891IsoCommaStackCore f g) :
    ∃ stack : EtaleStackOverField S1726K,
      stack.fiber.IsStack (SchemeOverField.etaleTopology S1726K) ∧
        ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
          Nonempty (↑(stack.fiber.obj U) ≌
            S1836IsoComma (f.map.app U).toFunctor (g.map.app U).toFunctor) := by
  obtain ⟨stack, e⟩ := h
  exact ⟨stack, stack.isStack, e⟩

/-- **The general two-fibre-product descent theorem supplies S1864's stack
half at the actual site.** -/
theorem S1891IsoCommaStackCore_of_descent
    (h : S1891StackTwoFiberProductDescent.{0})
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1891IsoCommaStackCore f g := by
  obtain ⟨P, hP, e⟩ :=
    h (C := SchemeOverField S1726K) (J := SchemeOverField.etaleTopology S1726K)
      A.source.fiber B.source.fiber C.source.fiber f.map g.map
      A.source.isStack B.source.isStack C.source.isStack
  exact ⟨{ fiber := P, isStack := hP }, fun U => e U⟩

/-- **S1864's first missing statement supplies the stack half.**  This shows
that the core statement is a lower bound for S1864's obligation: the general
two-fibre-product descent theorem is exactly what is used to fill the
`stack` and `fiberEquiv` fields. -/
theorem S1891IsoCommaStackCore_of_S1864FirstMissing
    (h : S1864FirstMissingIsoCommaStack) :
    ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
      S1891IsoCommaStackCore f g := by
  intro A B C f g
  obtain ⟨stack, e, _toA, _toB, _⟩ := h A B C f g
  exact ⟨stack, fun U => ⟨e U⟩⟩

/-- **The obligation itself supplies the stack half.** -/
theorem S1891IsoCommaStackCore_of_obligation {A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C}
    (D : S1864IsoCommaStackObligation f g) :
    S1891IsoCommaStackCore f g :=
  ⟨D.stack, fun U => ⟨D.fiberEquiv U⟩⟩

/-- **The core statement is exactly the instance of the general existence
statement at the étale site of §S1726K§.** -/
theorem S1891IsoCommaStackCore_iff_existsFor {A B C : S1728Cover}
    {f : S1728CoverMap A C} {g : S1728CoverMap B C} :
    S1891IsoCommaStackCore f g ↔
      S1891IsoCommaStackExistsFor (SchemeOverField.etaleTopology S1726K)
        A.source.fiber B.source.fiber C.source.fiber f.map g.map := by
  constructor
  · rintro ⟨stack, e⟩
    exact ⟨stack.fiber, stack.isStack, e⟩
  · rintro ⟨P, hP, e⟩
    exact ⟨{ fiber := P, isStack := hP }, e⟩

/-! ## 3. Non-vacuity: the identity-leg cases are unconditional -/

/-- **The identity-leg cases of the stack half are unconditional.**  This is
the non-vacuity check for the missing statement: in the cases already
constructed in S1836/S1864 (one leg is the identity cover map) an actual
stack with the required iso-comma fibres exists.  The general cospan is
exactly what the missing descent theorem has to supply. -/
theorem S1891IsoCommaStackCore_id_right {A C : S1728Cover}
    (f : S1728CoverMap A C) :
    S1891IsoCommaStackCore (B := C) f (S1641CoverMapId C) := by
  obtain ⟨D⟩ := S1864IdentityLegsNonvacuous.1 A C f
  exact S1891IsoCommaStackCore_of_obligation D

/-- The other identity-leg case. -/
theorem S1891IsoCommaStackCore_id_left {B C : S1728Cover}
    (g : S1728CoverMap B C) :
    S1891IsoCommaStackCore (A := C) (S1641CoverMapId C) g := by
  obtain ⟨D⟩ := S1864IdentityLegsNonvacuous.2 B C g
  exact S1891IsoCommaStackCore_of_obligation D

/-! ## 4. General identity-leg existence (arbitrary site) -/

/-- **The identity-leg case of the missing theorem at an arbitrary site.**  If
the right leg is the identity strong transformation of `F`, the iso-comma
pseudofunctor is equivalent to `G` itself, which is a stack by hypothesis.
This is a genuine special case of the missing existence statement, not a
restatement of it. -/
theorem S1891StackTwoFiberProductDescent_id_left
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (R : Pseudofunctor.StrongTrans G F) (hG : G.IsStack J) :
    S1891IsoCommaStackExistsFor J F G F (Pseudofunctor.StrongTrans.id F) R :=
  ⟨G, hG, fun U => ⟨S1836IsoCommaLeftIdEquiv ((R.app U).toFunctor)⟩⟩

/-- **The other identity-leg case at an arbitrary site.** -/
theorem S1891StackTwoFiberProductDescent_id_right
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (R : Pseudofunctor.StrongTrans F G) (hF : F.IsStack J) :
    S1891IsoCommaStackExistsFor J F G G R (Pseudofunctor.StrongTrans.id G) :=
  ⟨F, hF, fun U => ⟨S1836IsoCommaRightIdEquiv ((R.app U).toFunctor)⟩⟩

/-! ## 5. The case of a pointwise-equivalence leg -/

section EquivalenceLeg

variable {A B C : Type u} [Category.{u, u} A] [Category.{u, u} B] [Category.{u, u} C]

/-- If `L` is an equivalence, the second projection of the iso-comma is full. -/
instance S1891IsoCommaSndFull (L : A ⥤ C) (R : B ⥤ C) [L.IsEquivalence] :
    (S1836IsoCommaSnd L R).Full where
  map_surjective {X Y} g := by
    change X.obj.right ⟶ Y.obj.right at g
    haveI hX : IsIso X.obj.hom := X.2
    haveI hY : IsIso Y.obj.hom := Y.2
    obtain ⟨f, hf⟩ := L.map_surjective (X.obj.hom ≫ R.map g ≫ inv Y.obj.hom)
    refine ⟨ObjectProperty.homMk (CommaMorphism.mk f g ?_), ?_⟩
    · rw [hf]
      simp
    · rfl

/-- If `L` is an equivalence, the second projection of the iso-comma is
faithful. -/
instance S1891IsoCommaSndFaithful (L : A ⥤ C) (R : B ⥤ C) [L.IsEquivalence] :
    (S1836IsoCommaSnd L R).Faithful where
  map_injective {X Y} {f g} h := by
    change f.hom.right = g.hom.right at h
    haveI hY : IsIso Y.obj.hom := Y.2
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · apply L.map_injective
      apply (cancel_mono Y.obj.hom).mp
      calc
        L.map f.hom.left ≫ Y.obj.hom = X.obj.hom ≫ R.map f.hom.right := f.hom.w
        _ = X.obj.hom ≫ R.map g.hom.right := by rw [h]
        _ = L.map g.hom.left ≫ Y.obj.hom := g.hom.w.symm
    · exact h

/-- If `L` is an equivalence, the second projection of the iso-comma is
essentially surjective. -/
instance S1891IsoCommaSndEssSurj (L : A ⥤ C) (R : B ⥤ C) [L.IsEquivalence] :
    (S1836IsoCommaSnd L R).EssSurj where
  mem_essImage b := by
    let a := L.objPreimage (R.obj b)
    let e := L.objObjPreimageIso (R.obj b)
    exact ⟨⟨Comma.mk a b e.hom, e.isIso_hom⟩, ⟨Iso.refl b⟩⟩

instance S1891IsoCommaSndIsEquivalence (L : A ⥤ C) (R : B ⥤ C) [L.IsEquivalence] :
    (S1836IsoCommaSnd L R).IsEquivalence where

/-- **If the left leg is an equivalence, the iso-comma is equivalent to the
right factor.** -/
noncomputable def S1891IsoCommaSndEquiv (L : A ⥤ C) (R : B ⥤ C) [L.IsEquivalence] :
    S1836IsoComma L R ≌ B :=
  (S1836IsoCommaSnd L R).asEquivalence

/-- If `R` is an equivalence, the first projection of the iso-comma is full. -/
instance S1891IsoCommaFstFull (L : A ⥤ C) (R : B ⥤ C) [R.IsEquivalence] :
    (S1836IsoCommaFst L R).Full where
  map_surjective {X Y} g := by
    change X.obj.left ⟶ Y.obj.left at g
    haveI hX : IsIso X.obj.hom := X.2
    haveI hY : IsIso Y.obj.hom := Y.2
    obtain ⟨f, hf⟩ := R.map_surjective (inv X.obj.hom ≫ L.map g ≫ Y.obj.hom)
    refine ⟨ObjectProperty.homMk (CommaMorphism.mk g f ?_), ?_⟩
    · rw [hf]
      simp
    · rfl

/-- If `R` is an equivalence, the first projection of the iso-comma is
faithful. -/
instance S1891IsoCommaFstFaithful (L : A ⥤ C) (R : B ⥤ C) [R.IsEquivalence] :
    (S1836IsoCommaFst L R).Faithful where
  map_injective {X Y} {f g} h := by
    change f.hom.left = g.hom.left at h
    haveI hX : IsIso X.obj.hom := X.2
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact h
    · apply R.map_injective
      apply (cancel_epi X.obj.hom).mp
      calc
        X.obj.hom ≫ R.map f.hom.right = L.map f.hom.left ≫ Y.obj.hom := f.hom.w.symm
        _ = L.map g.hom.left ≫ Y.obj.hom := by rw [h]
        _ = X.obj.hom ≫ R.map g.hom.right := g.hom.w

/-- If `R` is an equivalence, the first projection of the iso-comma is
essentially surjective. -/
instance S1891IsoCommaFstEssSurj (L : A ⥤ C) (R : B ⥤ C) [R.IsEquivalence] :
    (S1836IsoCommaFst L R).EssSurj where
  mem_essImage a := by
    let b := R.objPreimage (L.obj a)
    let e := R.objObjPreimageIso (L.obj a)
    exact ⟨⟨Comma.mk a b e.symm.hom, e.symm.isIso_hom⟩, ⟨Iso.refl a⟩⟩

instance S1891IsoCommaFstIsEquivalence (L : A ⥤ C) (R : B ⥤ C) [R.IsEquivalence] :
    (S1836IsoCommaFst L R).IsEquivalence where

/-- **If the right leg is an equivalence, the iso-comma is equivalent to the
left factor.** -/
noncomputable def S1891IsoCommaFstEquiv (L : A ⥤ C) (R : B ⥤ C) [R.IsEquivalence] :
    S1836IsoComma L R ≌ A :=
  (S1836IsoCommaFst L R).asEquivalence

end EquivalenceLeg

/-- **The missing theorem in the case of a pointwise-equivalence left leg.**
If `L.app U` is an equivalence for every test object, the iso-comma
pseudofunctor is equivalent to `G` itself, so it is a stack as soon as `G`
is.  This is a genuine unconditional special case of the missing theorem. -/
theorem S1891StackTwoFiberProductDescent_of_left_equiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H)
    (hL : ∀ U, ((L.app U).toFunctor).IsEquivalence) (hG : G.IsStack J) :
    S1891IsoCommaStackExistsFor J F G H L R := by
  refine ⟨G, hG, fun U => ⟨?_⟩⟩
  letI := hL U
  exact (S1891IsoCommaSndEquiv (L.app U).toFunctor (R.app U).toFunctor).symm

/-- **The missing theorem in the case of a pointwise-equivalence right leg.** -/
theorem S1891StackTwoFiberProductDescent_of_right_equiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H)
    (hR : ∀ U, ((R.app U).toFunctor).IsEquivalence) (hF : F.IsStack J) :
    S1891IsoCommaStackExistsFor J F G H L R := by
  refine ⟨F, hF, fun U => ⟨?_⟩⟩
  letI := hR U
  exact (S1891IsoCommaFstEquiv (L.app U).toFunctor (R.app U).toFunctor).symm

/-! ## 6. The missing theorem implies its own interface form -/

/-- **From existence to the interface statement.**  If every cospan of
stacks has an iso-comma stack, then there is an interface (a pseudofunctor
with iso-comma values) whose pseudofunctor is a stack.  This is the precise
interface form of the missing theorem: it supplies a stack-valued
pseudofunctor, not the stackhood of an already given arbitrary interface. -/
theorem S1891IsoCommaPseudofunctor_exists_of_descent
    (h : S1891StackTwoFiberProductDescent.{u})
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F G H : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u})
    (L : Pseudofunctor.StrongTrans F H) (R : Pseudofunctor.StrongTrans G H)
    (hF : F.IsStack J) (hG : G.IsStack J) (hH : H.IsStack J) :
    ∃ I : S1891IsoCommaPseudofunctor F G H L R, I.P.IsStack J :=
  (S1891IsoCommaStackExistsFor_iff_interface J F G H L R).mp
    (h (C := C) J F G H L R hF hG hH)

/-! ## 7. The Mathlib API surface relevant to the missing theorem -/

#check @Pseudofunctor.IsStack
#check @Pseudofunctor.IsStack.of_isStackFor
#check @Pseudofunctor.isStackFor
#check @Pseudofunctor.isStackFor'
#check @Pseudofunctor.IsStackFor
#check @Pseudofunctor.IsPrestackFor
#check @Pseudofunctor.toDescentData
#check @Pseudofunctor.DescentData
#check @Pseudofunctor.isStackFor_iff
#check @Pseudofunctor.IsStackFor.isPrestackFor
#check @Pseudofunctor.IsStackFor.essSurj
#check @Comma.map
#check @Comma.mapLeftId
#check @Comma.mapLeftComp
#check @Comma.mapLeftEq
#check @Comma.fst
#check @Comma.snd

/-! ## 8. Checks and axiom audit -/

#check S1891IsoCommaStackExistsFor
#check S1891StackTwoFiberProductDescent
#check S1891IsoCommaPseudofunctor
#check S1891IsoCommaStackExistsFor_iff_interface
#check S1891IsoCommaStackCore
#check S1891IsoCommaStackCore.isStack
#check S1891IsoCommaStackCore_of_descent
#check S1891IsoCommaStackCore_of_S1864FirstMissing
#check S1891IsoCommaStackCore_of_obligation
#check S1891IsoCommaStackCore_iff_existsFor
#check S1891IsoCommaStackCore_id_right
#check S1891IsoCommaStackCore_id_left
#check S1891StackTwoFiberProductDescent_id_left
#check S1891StackTwoFiberProductDescent_id_right
#check S1891IsoCommaSndEquiv
#check S1891IsoCommaFstEquiv
#check S1891StackTwoFiberProductDescent_of_left_equiv
#check S1891StackTwoFiberProductDescent_of_right_equiv
#check S1891IsoCommaPseudofunctor_exists_of_descent

#print axioms S1891IsoCommaStackExistsFor_iff_interface
#print axioms S1891IsoCommaStackCore_of_descent
#print axioms S1891IsoCommaStackCore_of_S1864FirstMissing
#print axioms S1891IsoCommaStackCore_iff_existsFor
#print axioms S1891IsoCommaStackCore_id_right
#print axioms S1891IsoCommaStackCore_id_left
#print axioms S1891StackTwoFiberProductDescent_id_left
#print axioms S1891StackTwoFiberProductDescent_id_right
#print axioms S1891IsoCommaSndEquiv
#print axioms S1891IsoCommaFstEquiv
#print axioms S1891StackTwoFiberProductDescent_of_left_equiv
#print axioms S1891StackTwoFiberProductDescent_of_right_equiv
#print axioms S1891IsoCommaPseudofunctor_exists_of_descent

end LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual
