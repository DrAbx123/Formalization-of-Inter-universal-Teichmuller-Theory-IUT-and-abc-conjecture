import tmp.sheaf.xif.paper.S1963SignActionAssemblyActual
import tmp.sheaf.xif.paper.S1964QuotientCFActual
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# S1971: the pointwise 2-colimit of the sign action, and the exact first missing

## The problem

S1964 reduced the paper's quotient C_F = X_F / {+-1} to the quotient structure
S1964QuotientStructure.  The route to that structure has four steps:

1. the pointwise lax colimit (Grothendieck construction) of the sign action on
   the Cat-valued fibers of X_F;
2. functoriality/coherence of this colimit in the test scheme;
3. Pseudofunctor.IsStack for the resulting pseudofunctor (stackification);
4. the bicategorical universal property descend / factor / descendTwoCell /
   twoCellExt.

This file settles step 1 for the actual action and isolates the exact first
missing datum of steps 2-4.  It does NOT construct or postulate a quotient.

## What is proved

* The actual sign group acts on the U-points of the S1726 affine model by
  postcomposition with the actual elliptic involution S1898AffineEndo
  (section 1).  Its multiplication law follows from S1932AffineEndo_comp,
  the actual computation that [-1]^2 = 1.

* At each test object U the pointwise Grothendieck construction of this
  action is the action category of the group action on the type of U-points;
  its objects are U-points and its morphisms P -> Q are group elements g
  with g . P = Q (section 2).  This is the honest pointwise lax colimit,
  not an orbit set: at a fixed point the stabilizer is the full sign group.

* A generic functoriality lemma on action categories: an equivariant map of
  group actions induces a functor of action categories.  Applied to the
  strict commutativity of precomposition and postcomposition, it gives the
  restriction functor of the pointwise colimit along every test-scheme
  morphism (section 3).

## The exact first missing

The first missing datum is the global pseudofunctor whose fiber at U is the
pointwise colimit, i.e. the assembly of the restriction functors of section 3
into one category-valued pseudofunctor with coherent mapId/mapComp/
associativity/unitor data.  It is stated exactly as
S1971FunctorialPointwiseColimit (section 4).  It is not proved here: the
pointwise construction gives the fibers, but the strict functoriality proof
requires coherence equations between functors of action categories which are
not formalized in this tree.

Once that functor is available, the next missing datum is descent, Q.IsStack
for the etale topology (S1971Stackification).  This is not a consequence of
the pointwise construction: the action category at U sees only the trivial
sign-torsor on U, while an etale stack must also see every nontrivial
sign-torsor.  Mathlib has no stackification of Cat-valued pseudofunctors.

Even with an IsStack quotient fiber, step 4 -- the sign-invariant quotient
morphism and its universal property -- is still a separate datum.  The
consumer at the end records that a stack quotient together with that witness
yields S1964QuotientStructure; nothing in this file pretends to supply the
fibers, the stack condition or the witness.

No sorry, admit, new axiom, PUnit/ULift placeholder or arbitrary IsStack
instance is used.  The final #print axioms block records the footprint.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual
open LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual
open LeanFormal.IUT.XiFPaper.S1963SignActionAssemblyActual
open LeanFormal.IUT.XiFPaper.S1964QuotientCFActual

/-! ## 1. The actual sign action on test-scheme points -/

/-- The scheme automorphism of the sign element: the identity on 1 and the
actual elliptic involution S1898AffineEndo on the nontrivial element. -/
noncomputable def S1971SchemeAut (g : SignGroup) :
    S1726AffineOver ⟶ S1726AffineOver :=
  if g = 1 then 𝟙 S1726AffineOver else S1898AffineEndo

theorem S1971SchemeAut_one : S1971SchemeAut 1 = 𝟙 S1726AffineOver := by
  simp [S1971SchemeAut]

theorem S1971SchemeAut_ne {g : SignGroup} (hg : g ≠ 1) :
    S1971SchemeAut g = S1898AffineEndo := by
  simp [S1971SchemeAut, hg]

theorem S1971SchemeAut_gen :
    S1971SchemeAut (Multiplicative.ofAdd (1 : ZMod 2)) = S1898AffineEndo := by
  apply S1971SchemeAut_ne
  exact S1963SignGroup_generator_ne

/-- The multiplication law of the actual scheme action.  The group is ZMod 2,
so the only nontrivial case is the actual computation [-1] ; [-1] = 1
(S1932AffineEndo_comp). -/
theorem S1971SchemeAut_mul (g h : SignGroup) :
    S1971SchemeAut (g * h) = S1971SchemeAut h ≫ S1971SchemeAut g := by
  by_cases hg : g = 1
  · subst g
    simp [S1971SchemeAut]
  · by_cases hh : h = 1
    · subst h
      simp [S1971SchemeAut]
    · have hgh : g * h = 1 := S1963SignGroup_mul_eq_one hg hh
      rw [hgh, S1971SchemeAut_one, S1971SchemeAut_ne hg, S1971SchemeAut_ne hh]
      exact (S1932AffineEndo_comp).symm

/-- The actual sign action on the type of U-points: postcomposition with
the scheme automorphism of the sign element. -/
instance S1971PointSMul (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    SMul SignGroup (Opposite.unop U.as ⟶ S1726AffineOver) where
  smul g P := P ≫ S1971SchemeAut g

/-- The sign action on U-points is a genuine MulAction. -/
instance S1971PointMulAction (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) :
    MulAction SignGroup (Opposite.unop U.as ⟶ S1726AffineOver) where
  one_smul P := by
    change P ≫ S1971SchemeAut 1 = P
    rw [S1971SchemeAut_one, Category.comp_id]
  mul_smul g h P := by
    change P ≫ S1971SchemeAut (g * h) = (P ≫ S1971SchemeAut h) ≫ S1971SchemeAut g
    rw [S1971SchemeAut_mul, Category.assoc]

/-! ## 2. The pointwise lax colimit as an action category -/

/-- The pointwise 2-colimit of the sign action at a test object U.
This is the action category (equivalently, the Grothendieck construction) of
the sign action on the type of U-points. -/
noncomputable def S1971PointwiseQuotient
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ) : Cat :=
  Cat.of (ActionCategory SignGroup (Opposite.unop U.as ⟶ S1726AffineOver))

/-- The morphisms of the pointwise colimit are the action-groupoid
morphisms: a morphism P -> Q is a sign element g with g . P = Q.
In particular the pointwise colimit is not the orbit set of the action. -/
theorem S1971PointwiseQuotient_hom
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    (P Q : ActionCategory SignGroup (Opposite.unop U.as ⟶ S1726AffineOver)) :
    (P ⟶ Q) = { g : SignGroup // g • P.back = Q.back } :=
  ActionCategory.hom_as_subtype (M := SignGroup)
    (X := Opposite.unop U.as ⟶ S1726AffineOver) P Q

/-- Fixed points retain the whole stabilizer.  If a point is fixed by the
nontrivial sign element, then its endomorphism type in the pointwise colimit
contains a nonidentity automorphism.  Hence the action category is genuinely
stacky at fixed points, and cannot be the coarse orbit set. -/
theorem S1971PointwiseQuotient_fixed_nontrivial_aut
    (U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ)
    {P : ActionCategory SignGroup (Opposite.unop U.as ⟶ S1726AffineOver)}
    (hP : (Multiplicative.ofAdd (1 : ZMod 2)) • P.back = P.back) :
    ∃ φ : P ⟶ P, φ ≠ 𝟙 _ := by
  refine ⟨⟨Multiplicative.ofAdd (1 : ZMod 2), hP⟩, ?_⟩
  intro h
  have hval := congrArg Subtype.val h
  exact S1963SignGroup_generator_ne hval

/-! ## 3. Functoriality on action categories -/

/-- An equivariant map of group actions induces a functor of action
categories.  This is the functoriality of the Grothendieck construction for
a strict action of a group on a type, stated generically. -/
noncomputable def S1971ActionMap {M : Type} [Monoid M] {X Y : Type}
    [MulAction M X] [MulAction M Y]
    (f : X → Y) (hf : ∀ (g : M) (x : X), f (g • x) = g • f x) :
    ActionCategory M X ⥤ ActionCategory M Y :=
  NatTrans.mapElements (C := SingleObj M) (F := actionAsFunctor M X)
    (G := actionAsFunctor M Y) {
    app := fun a => ↾(fun x : (actionAsFunctor M X).obj a => f x)
    naturality := by
      intro a b g
      ext x
      simp only [actionAsFunctor_map]
      exact hf g x }

@[simp] lemma S1971ActionMap_obj_back {M : Type} [Monoid M] {X Y : Type}
    [MulAction M X] [MulAction M Y] (f : X → Y)
    (hf : ∀ (g : M) (x : X), f (g • x) = g • f x)
    (p : ActionCategory M X) :
    ((S1971ActionMap (M := M) f hf).obj p).back = f p.back := by
  cases p with
  | mk X x => rfl

@[simp] lemma S1971ActionMap_map_val {M : Type} [Monoid M] {X Y : Type}
    [MulAction M X] [MulAction M Y] (f : X → Y)
    (hf : ∀ (g : M) (x : X), f (g • x) = g • f x)
    {p q : ActionCategory M X} (φ : p ⟶ q) :
    ((S1971ActionMap (M := M) f hf).map φ).val = φ.val := by
  cases φ with
  | mk g h => rfl

@[simp] lemma S1971ActionCategory_eqToHom_val {M : Type} [Monoid M] {X : Type}
    [MulAction M X] {p q : ActionCategory M X} (h : p = q) :
    (eqToHom h).val = 1 := by
  subst h
  rfl

/-- Restriction of the pointwise colimit along a morphism of test schemes.
This is the single-morphism part of step 2. -/
noncomputable def S1971PrecompFunctor
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (f : U ⟶ V) :
    S1971PointwiseQuotient U ⥤ S1971PointwiseQuotient V := by
  letI := S1971PointMulAction U
  letI := S1971PointMulAction V
  exact S1971ActionMap (M := SignGroup)
    (X := Opposite.unop U.as ⟶ S1726AffineOver)
    (Y := Opposite.unop V.as ⟶ S1726AffineOver)
    (fun P => f.as.unop ≫ P) (by
      intro g P
      change (f.as.unop ≫ P) ≫ S1971SchemeAut g =
        f.as.unop ≫ (P ≫ S1971SchemeAut g)
      rw [Category.assoc])

@[simp] lemma S1971PrecompFunctor_obj_back
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (f : U ⟶ V)
    (P : S1971PointwiseQuotient U) :
    ((S1971PrecompFunctor f).obj P).back = f.as.unop ≫ P.back := by
  dsimp [S1971PrecompFunctor]
  rw [S1971ActionMap_obj_back]

@[simp] lemma S1971PrecompFunctor_map_val
    {U V : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (f : U ⟶ V)
    {P Q : S1971PointwiseQuotient U} (φ : P ⟶ Q) :
    ((S1971PrecompFunctor f).map φ).val = φ.val := by
  dsimp [S1971PrecompFunctor]
  rw [S1971ActionMap_map_val]

/-! ## 4. The exact first missing: global functoriality and stackification -/

/-- The first missing datum after the pointwise construction.  A
category-valued pseudofunctor on the etale site whose fiber at every test
object is the pointwise lax colimit constructed in section 2.  The
restriction functors of section 3 exist, but their coherence into a single
pseudofunctor is not formalized. -/
def S1971FunctorialPointwiseColimit : Prop :=
  ∃ Q : EtaleStackPseudofunctor S1726K,
    ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (Q.obj U) (S1971PointwiseQuotient U))

/-- The second missing datum: descent/stackification.  Even a functorial
pointwise colimit is only a prestack: its U-points see the trivial sign
torsor, not arbitrary etale sign-torsors.  The etale stack condition is a
separate input. -/
def S1971Stackification (Q : EtaleStackPseudofunctor S1726K) : Prop :=
  Q.IsStack (SchemeOverField.etaleTopology S1726K)

/-- The exact missing stack quotient fiber: a functorial pointwise colimit
which is an etale stack. -/
def S1971QuotientStack : Prop :=
  ∃ Q : EtaleStackPseudofunctor S1726K,
    (∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (Q.obj U) (S1971PointwiseQuotient U))) ∧
    S1971Stackification Q

/-- The stack quotient datum is exactly the functorial pointwise colimit plus
the stack condition; this is a definitional unfolding, not a construction. -/
theorem S1971QuotientStack_iff :
    S1971QuotientStack ↔
      ∃ Q : EtaleStackPseudofunctor S1726K,
        (∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
          Nonempty (CategoryTheory.Equivalence (Q.obj U) (S1971PointwiseQuotient U))) ∧
        S1971Stackification Q :=
  Iff.rfl

/-- The first missing step is not a consequence of having the pointwise
fibers: S1971FunctorialPointwiseColimit is an additional existential over
pseudofunctors. -/
def S1971FirstMissingStep : Prop :=
  S1971FunctorialPointwiseColimit

/-! ## 5. Consumer: a stack quotient plus the sign-invariant witness -/

/-- The actual stack quotient package needed by S1964: a hyperbolic orbicurve
whose fiber is the sign quotient (with the pointwise colimit as its fibers),
together with the sign-invariant quotient morphism and its bicategorical
universal property.  This is the four-step target of S1964, packaged over the
concrete pointwise colimit. -/
structure S1971StackQuotientWitness (l : PrimeGeFive)
    (A : Iut.OrbicurveSignAction S1726Orbicurve) where
  /-- The quotient orbicurve. -/
  cF : Iut.HyperbolicOrbicurve (S1732A l).F
  /-- Its fiber is the pointwise colimit at every test object. -/
  pointwise : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
    Nonempty (CategoryTheory.Equivalence
      (cF.stack.fiber.obj U) (S1971PointwiseQuotient U))
  /-- The sign-invariant quotient morphism. -/
  quotient : Iut.OrbicurveSignInvariantMorphism A cF
  /-- The bicategorical universal property. -/
  witness : Iut.OrbicurveSignQuotientWitness A quotient

/-- A stack quotient witness yields the S1964 quotient structure.  The
signature label is deliberately not part of this reduction. -/
def S1971StackQuotientWitness.toS1964 {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (W : S1971StackQuotientWitness l A) : S1964QuotientStructure l A :=
  ⟨W.cF, W.quotient, W.witness⟩

/-- The first missing after S1964 is still open.  The existence of a
stack quotient witness implies the S1964 quotient structure; the converse is
not asserted, because the S1964 quotient fiber need not be the concrete
pointwise colimit without the global functoriality and stackification. -/
theorem S1964FirstMissing_ofStackQuotientWitness {l : PrimeGeFive}
    {A : Iut.OrbicurveSignAction S1726Orbicurve}
    (h : Nonempty (S1971StackQuotientWitness l A)) : S1964FirstMissing l A :=
  h.elim fun W => ⟨W.toS1964⟩

/-! ## 6. Axiom footprint -/

#print axioms S1971SchemeAut
#print axioms S1971SchemeAut_mul
#print axioms S1971PointMulAction
#print axioms S1971PointwiseQuotient
#print axioms S1971PointwiseQuotient_hom
#print axioms S1971PointwiseQuotient_fixed_nontrivial_aut
#print axioms S1971ActionMap
#print axioms S1971ActionMap_obj_back
#print axioms S1971ActionMap_map_val
#print axioms S1971ActionCategory_eqToHom_val
#print axioms S1971PrecompFunctor
#print axioms S1971PrecompFunctor_obj_back
#print axioms S1971PrecompFunctor_map_val
#print axioms S1971QuotientStack_iff
#print axioms S1971StackQuotientWitness.toS1964
#print axioms S1964FirstMissing_ofStackQuotientWitness

end LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual

end