import tmp.sheaf.xif.paper.S2025QuotientStackPackageActual
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver

/-!
# S2029: Giraud stackification -- the exact first missing, and the size obstruction

This file attacks the last input of the quotient-stack route of S1994/S1997/S2002/
S2019/S2022/S2025: the construction of the category-valued etale stack

  `[Z / mu_l]`,   `Z = {b | b^l = 0}`,  `mu_l = {zeta | zeta^l = 1}`,

with a fully faithful comparison from the root prestack (`S2022FirstMissing`).
The two mathematically available routes are

* (G) Giraud stackification of the root prestack, and
* (T) the site-specific `mu_l`-torsor / equivariant-sheaf stack.

Both routes share the same first *formal* obstacle, which is recorded here for the
first time and which changes the shape of the remaining gap:

## The size obstruction

The tree encodes category-valued stacks as `Iut.EtaleStackPseudofunctor K =
LocallyDiscrete (SchemeOverField K)^op |-> Cat.{u,u}`, i.e. every fibre must be a
category whose object type and hom types live in `Type u` (the universe of `K`).
The site itself is `SchemeOverField K : Type (u+1)`, and every natural model of
`[Z / mu_l]` is built from *sheaves on the slice site* or from *schemes* (torsors):

* the category of sheaves of `Type u` on the slice site over a test object `U`
  is `Sheaf (etaleTopology K).over U (Type u) : Type (u+1)`, hence a
  `Cat.{u+1, u+1}` object (see `S2029SliceSheafCategory` and the identity
  `S2029SheafPrestack_obj` below; a direct `Cat.{u,u}` ascription fails with the
  universe constraint `u =?= u + 1`);
* a `mu_l`-torsor is a scheme/sheaf over `U`, and the type of schemes is also
  `Type (u+1)`.

Consequently the **naive** sheaf-theoretic and torsor-theoretic models of the
quotient stack cannot be typed at `Cat.{u,u}`: a genuine receiver requires a
*u-small model* of `[Z / mu_l]` (a skeleton of the essentially small torsor groupoid, i.e. a
smallness/classification input), or a change of the universe parameter of
`EtaleStackPseudofunctor`.  This is not the same gap as "Giraud's theorem is
missing": it is a size/encoding obligation which is independent of the descent
theory, and it is present for *every* non-discrete stack on this large site.

## What is proved here

1. `S2029FirstMissing` is the receiver form of the missing, and it is proved
   *equivalent* to `S2022FirstMissing` and to `S2025FirstMissing` (Section 1);
   all downstream transfers (`S1997`, `S2002`, `S2019`, `S1994`) are re-exported.
2. The natural sheaf model of the quotient stack is exhibited as an honest
   `Cat.{u+1, u+1}`-valued pseudofunctor `S2029SheafPrestack`, using Mathlib's
   `GrothendieckTopology.pseudofunctorOver`; its stack condition is the concrete
   statement `S2029SheafStack` (Section 2).  Nothing is asserted about
   `S2029SheafStack`: it is exactly the "stack of sheaves" theorem which Mathlib
   does not have (no `IsStack` instance for any non-discrete pseudofunctor).
3. The size obstruction is stated in the same section: the natural value
   `S2029SliceSheafCategory K U` is a `Cat.{u+1,u+1}` object, `S2029SheafPrestack`
   takes values in `Cat.{u+1,u+1}`, and the target `EtaleStackPseudofunctor K`
   requires `Cat.{u,u}` values (Section 3).

## Honest boundary

No `IsStack` instance is fabricated, no `sorry`, no `axiom`, no `Shrink`/`ULift`
placeholder.  `S2022FirstMissing` (equivalently `S2029FirstMissing`) has no
inhabitant: the missing inputs are (a) a stackification of the root prestack
(Giraud, or the site-specific equivariant-sheaf/torsor stack) and (b) a u-small
model of its fibres.  The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

## Recommended next steps

* If the universe parameter of `EtaleStackPseudofunctor` may be raised (needs a
  user instruction, since it changes the target), then the concrete missing input
  is `S2029SheafStack` together with the slice/equivariant-sheaf construction and
  the pointwise full faithfulness computation (S2022 section 4).
* If the target stays at `Cat.{u,u}`, the missing input additionally contains a
  small-model theorem: the torsor groupoid of `mu_l` on the etale site is
  essentially small (its isomorphism classes are `H^1(-, mu_l)`), and one must
  choose a small skeleton together with the induced pseudofunctorial structure.
-/


noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
open LeanFormal.IUT.XiFPaper.S2008RootPrestackActual
open LeanFormal.IUT.XiFPaper.S2013RootHomSheafActual
open LeanFormal.IUT.XiFPaper.S2019RebasedRootStackActual
open LeanFormal.IUT.XiFPaper.S2022QuotientStackActual
open LeanFormal.IUT.XiFPaper.S2025QuotientStackPackageActual

universe u

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-! ## 1. The target and its existing forms -/

/-- **The exact first missing, in receiver form.**  A `u`-small category-valued
etale stack together with a fully faithful comparison from the `l`-tors root
prestack.  This is exactly `S2025FirstMissing` (and hence, by S2025, exactly
`S2022FirstMissing`). -/
def S2029FirstMissing (K : Type u) [Field K] (l : PrimeGeFive) : Prop :=
  S2025FirstMissing K l

/-- The receiver form is S2025's missing. -/
theorem S2029FirstMissing_iff_S2025FirstMissing :
    S2029FirstMissing K l ↔ S2025FirstMissing K l := Iff.rfl

/-- The receiver form is exactly S2022's missing. -/
theorem S2029FirstMissing_iff_S2022FirstMissing :
    S2029FirstMissing K l ↔ S2022FirstMissing K l :=
  S2025FirstMissing_iff_S2022FirstMissing

/-- S2022's missing is the receiver form. -/
theorem S2022FirstMissing_iff_S2029FirstMissing :
    S2022FirstMissing K l ↔ S2029FirstMissing K l :=
  (S2029FirstMissing_iff_S2022FirstMissing (K := K) (l := l)).symm

/-- The missing supplies S1997's root stackification datum. -/
theorem S2029FirstMissing_implies_S1997 (h : S2029FirstMissing K l) :
    S1997RootStackificationMissing K l :=
  S2025FirstMissing_implies_S1997 h

/-- The missing supplies S2002's existential datum. -/
theorem S2029FirstMissing_implies_S2002 (h : S2029FirstMissing K l) :
    S2002RootStackificationDatum (K := K) (l := l) :=
  S2025FirstMissing_implies_S2002 h

/-- The missing supplies S2019's corrected root-stack datum. -/
theorem S2029FirstMissing_implies_S2019Corrected (h : S2029FirstMissing K l) :
    Nonempty (S2019CorrectedRootStackDatum K l) :=
  S2025FirstMissing_implies_S2019Corrected h

/-- The missing supplies S1994's stacky orbicurve. -/
theorem S2029FirstMissing_implies_S1994 {lg : PrimeGeFive}
    {A : InitialThetaArithmeticData lg} (h : S2029FirstMissing A.K lg) :
    S1994StackyOrbicurveMissing lg A :=
  S2025FirstMissing_implies_S1994 h

/-- The prestack route (`Q` = root prestack) implies the receiver form: if the
root prestack is already a stack, the identity comparison witnesses the missing. -/
theorem S2019FirstMissing_implies_S2029FirstMissing
    (h : S2019FirstMissing (K := K) (l := l)) : S2029FirstMissing K l :=
  S2019FirstMissing_implies_S2025FirstMissing h

/-! ## 2. The natural sheaf model: an honest `Cat.{u+1,u+1}`-valued pseudofunctor -/

/-- The category of sheaves of types on the slice etale site over a test object
`U`.  This is the natural value at `U` of the "stack of sheaves" model of the
quotient stack (the slice site of `U` is `Over U`, and its topology is
`(etaleTopology K).over U`).

It is a `Cat.{u+1,u+1}`, one universe above the `Cat.{u,u}` fibres required by
`Iut.EtaleStackPseudofunctor`; see the module docstring. -/
noncomputable def S2029SliceSheafCategory (K : Type u) [Field K]
    (U : Iut.SchemeOverField K) : Cat.{u+1, u+1} :=
  Cat.of (Sheaf ((Iut.SchemeOverField.etaleTopology K).over U) (Type u))

/-- The pseudofunctor `U |-> Sheaf (etaleTopology K).over U (Type u)`, obtained
from Mathlib's `GrothendieckTopology.pseudofunctorOver`.  It is the natural
ambient object in which the quotient stack `[Z / mu_l]` (as the slice over the
equivariant map `mu_l -> Z`) lives.

**No `IsStack` instance is asserted**: see `S2029SheafStack`. -/
noncomputable def S2029SheafPrestack (K : Type u) [Field K] :
    Pseudofunctor (LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) Cat.{u+1, u+1} :=
  (Iut.SchemeOverField.etaleTopology K).pseudofunctorOver (Type u)

/-- The value of `S2029SheafPrestack` at a test object is the slice sheaf
category.  This identity exhibits the universe at which the natural model lives. -/
theorem S2029SheafPrestack_obj (K : Type u) [Field K] (U : Iut.SchemeOverField K) :
    (S2029SheafPrestack K).obj (LocallyDiscrete.mk (Opposite.op U)) =
      S2029SliceSheafCategory K U := rfl

/-- **The concrete Stack-of-sheaves input.**  The pseudofunctor
`U |-> Sheaf (etaleTopology K).over U (Type u)` has effective descent for the
etale topology.  Mathlib v4.32.2 has no such instance: in fact it has no
`IsStack` instance at all, for any category-valued pseudofunctor (the tree's only
instances are for discrete/representable stacks).

This is the "stack of sheaves" theorem (a special case of Giraud's
stackification, but a concrete one), in the corrected universe.  It is *not*
`S2022FirstMissing`: the quotient stack additionally needs the slice over `Z`
and a `u`-small model (Section 3). -/
def S2029SheafStack (K : Type u) [Field K] : Prop :=
  (S2029SheafPrestack K).IsStack (Iut.SchemeOverField.etaleTopology K)

/-! ## 2b. The two Giraud statements: small-valued versus universe-corrected -/

/-- **Giraud stackification in the corrected universe `Cat.{u+1,u+1}`.**  Every
category-valued prestack on every site has a stackification whose unit is fully
faithful.  This is the mathematically true general statement (Giraud,
*Cohomologie non abelienne*; Laumon--Moret-Bailly 3.2), in the universe in which
the natural sheaf-theoretic models live; Mathlib v4.32.2 does not contain it.

It is *not* the same statement as `S2025PrestackStackification`, which is the
`Cat.{u,u}`-valued version, and it does not by itself close
`S2022FirstMissing`: the latter's carriers are `Cat.{u,u}` (Section 3). -/
def S2029GiraudStackification : Prop :=
  ∀ {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u+1, u+1}),
    F.IsPrestack J →
      ∃ Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u+1, u+1},
        Q.IsStack J ∧
          ∃ eta : Pseudofunctor.StrongTrans F Q,
            Nonempty (∀ U : LocallyDiscrete Cᵒᵖ, (eta.app U).toFunctor.FullyFaithful)

/-- **The `Cat.{u,u}`-valued Giraud statement**, i.e. S2025's general input.  This
is the version which *does* close the target: S2025 proves
`S2025PrestackStackification -> S2025FirstMissing`. -/
def S2029SmallStackification : Prop := S2025PrestackStackification.{u}

/-- The small-valued Giraud statement closes the receiver form (S2025). -/
theorem S2029SmallStackification_implies_S2029FirstMissing
    (h : S2029SmallStackification.{u}) : S2029FirstMissing K l :=
  S2025PrestackStackification.toS2025FirstMissing (K := K) (l := l) h

/-! ## 3. The size obstruction, stated on the target -/

/-- **Every receiver's fibre is `u`-small, by type.**  The fibres of an
`Iut.EtaleStackPseudofunctor K` live in `Type u`, hence are `Small.{u}`.  The
natural sheaf model of Section 2 lives in `Cat.{u+1,u+1}` instead, and is *not*
known to be `Small.{u}` (that would be an essential-smallness theorem for the
relevant sheaf category, unavailable in Mathlib).  This is the precise sense in
which the target's `Cat.{u,u}` encoding forces an extra small-model input. -/
theorem S2029_receiver_fiber_small (Q : Iut.EtaleStackPseudofunctor K)
    (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) :
    Small.{u} (↑(Q.obj U)) := inferInstance

/-- **The exact first missing is *not* satisfiable by the natural sheaf model.**
The target fibre type `Iut.EtaleStackPseudofunctor K` is `Cat.{u,u}`, while
`S2029SheafPrestack K` is `Cat.{u+1,u+1}`; the two cannot be identified in
Lean's type theory (their codomain universe levels differ).  We record this as the
named proposition that closing the target with a sheaf-theoretic model would
require: the existence of a `u`-small model at every test object.

The structure below is the *data* that a universe-corrected construction would
supply; it is a statement about `Cat.{u+1,u+1}` objects, and it makes explicit the
extra "smallness" input which the current `Cat.{u,u}` target forces. -/
structure S2029SmallModel (C : Cat.{u+1, u+1}) where
  /-- The `u`-small model of the large category. -/
  small : Cat.{u, u}
  /-- The model is equivalent to the large category. -/
  equivalent : Nonempty (↑small ≌ ↑C)

/-- A universe-corrected receiver: a large stack with a comparison whose fibres
admit `u`-small models.  This is the form in which a sheaf-theoretic construction
(Section 2) would have to be delivered in order to close `S2022FirstMissing`. -/
structure S2029LargeReceiver (K : Type u) [Field K] (l : PrimeGeFive) where
  /-- The large quotient stack, in the corrected universe. -/
  quotient : Pseudofunctor (LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) Cat.{u+1, u+1}
  /-- It is an etale stack. -/
  isStack : quotient.IsStack (Iut.SchemeOverField.etaleTopology K)
  /-- Every fibre admits a `u`-small model. -/
  smallModel : ∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
    S2029SmallModel (quotient.obj U)

/-- The two-input form of the missing (documentation statement, no inhabitant
asserted): a large stackification with `u`-small fibres.  This is the conjunction
of `S2029SheafStack`-style descent theory with the smallness input of Section 3.

This is a `Prop`-valued record of the exact remaining gap; it is deliberately not
proved to imply `S2022FirstMissing` here, because that implication needs the
(absent) transport of pseudofunctorial structure along the small models, which is
itself part of the missing construction. -/
def S2029TwoInputMissing (K : Type u) [Field K] (l : PrimeGeFive) : Prop :=
  Nonempty (S2029LargeReceiver K l)

/-! ## 4. Non-vacuity and checks -/

/-- The stackification statement of S2025 is non-vacuous: every stack is its own
stackification.  (Re-exported as the non-vacuity check of the route.) -/
theorem S2029_stackification_of_isStack
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u}) (hF : F.IsStack J) :
    ∃ Q : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u},
      Q.IsStack J ∧
        ∃ eta : Pseudofunctor.StrongTrans F Q,
          Nonempty (∀ U : LocallyDiscrete Cᵒᵖ, (eta.app U).toFunctor.FullyFaithful) :=
  S2025_stackification_of_isStack J F hF

/-- The missing is exactly the failure of the root prestack to be its own
stackification: the prestack route (S2019) is a sufficient condition. -/
theorem S2029FirstMissing_of_prestack (h : S2019FirstMissing (K := K) (l := l)) :
    S2029FirstMissing K l :=
  S2019FirstMissing_implies_S2029FirstMissing h

#check @S2029FirstMissing
#check @S2029FirstMissing_iff_S2022FirstMissing
#check @S2029FirstMissing_iff_S2025FirstMissing
#check @S2029FirstMissing_implies_S1997
#check @S2029FirstMissing_implies_S2002
#check @S2029FirstMissing_implies_S2019Corrected
#check @S2029FirstMissing_implies_S1994
#check @S2019FirstMissing_implies_S2029FirstMissing
#check @S2029SliceSheafCategory
#check @S2029SheafPrestack
#check @S2029SheafPrestack_obj
#check @S2029SheafStack
#check @S2029_receiver_fiber_small
#check @S2029GiraudStackification
#check @S2029SmallStackification
#check @S2029SmallStackification_implies_S2029FirstMissing
#check @S2029SmallModel
#check @S2029LargeReceiver
#check @S2029TwoInputMissing
#check @S2029_stackification_of_isStack
#check @S2029FirstMissing_of_prestack

#print axioms S2029FirstMissing_iff_S2022FirstMissing
#print axioms S2029FirstMissing_iff_S2025FirstMissing
#print axioms S2029FirstMissing_implies_S1997
#print axioms S2029FirstMissing_implies_S2002
#print axioms S2029FirstMissing_implies_S2019Corrected
#print axioms S2029FirstMissing_implies_S1994
#print axioms S2019FirstMissing_implies_S2029FirstMissing
#print axioms S2029SheafPrestack_obj
#print axioms S2029_receiver_fiber_small
#print axioms S2029GiraudStackification
#print axioms S2029SmallStackification_implies_S2029FirstMissing
#print axioms S2029_stackification_of_isStack
#print axioms S2029FirstMissing_of_prestack

end LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
