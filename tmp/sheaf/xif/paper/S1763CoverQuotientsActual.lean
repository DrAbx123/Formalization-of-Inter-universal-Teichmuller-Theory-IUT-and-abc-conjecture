/-
# S1763: finite group quotients and mono direct summands on the actual S1728 cover category

## Scope

S1736 reduced the two remaining PreGalois fields on the actual
`Category.{u+1,u+1}` cover category of S1728 to the propositions

* `S1736FiniteGroupQuotientObligation`:
  for every finite group `G` and every functor `D : SingleObj G ⥤ C`,
  a colimit of `D`;
* `S1736MonoDirectSummandObligation`:
  every mono `i : A ⟶ B` is the first inclusion of a binary coproduct.

This file attacks exactly those two fields on the actual category
`S1728CoverCategory11 : Category.{u+1,u+1} (OrbicurveFiniteEtaleCover X)`.
It does not introduce a new cover category, a new hom relation, a fake
colimit, a fake complement, or an axiom.

## Result

Constructed unconditionally in this file:

* `SingleObj G` is a connected index category, hence the **trivial action**
  `(Functor.const (SingleObj G)).obj A` has an actual colimit: the object
  `A` with the identity cocone (`S1763TrivialActionQuotient`,
  `S1763TrivialActionQuotientCocone`).  This is the quotient of a cover by
  the trivial action, and it is a genuine colimit, not a placeholder.
* If an object `A` is initial, every mono `i : A ⟶ B` is a binary coproduct
  inclusion with complement `B` and second leg `𝟙 B`
  (`monoDirectSummand_of_initial_domain`); specialised to the actual cover
  category in `S1763MonoSplitting_at_initial`.

Constructed conditionally on S1736's identity-finite-etale input:

* every action whose object is the terminal cover has a colimit, namely the
  terminal cover (`S1763TerminalActionQuotient`).  The only hypothesis beyond
  that input is that the functor's object is the terminal cover.

Reduced to exact data, with both directions proved:

* `S1763FiniteGroupQuotientData` is equivalent to the literal S1736
  quotient field (`S1763FiniteGroupQuotientData_iff`);
* `S1763MonoDirectSummandData` is equivalent to the literal S1736 mono field
  (`S1763MonoDirectSummandData_iff`);
* the two data, together with the three other S1736 inputs, assemble the
  actual S1736 PreGalois obligation (`S1763PreGaloisCategoryOfInputs`).

## Exact first missing

The remaining content is not a bookkeeping gap.  It is the geometric
construction of the quotient object and of the complement:

1. **Finite group quotients.**  For a nontrivial action `D` of a finite group
   on a nonterminal cover, the required datum is an actual cover `Q` and a
   colimiting cocone over `D` with point `Q`.  This is
   `S1763QuotientCoverRequired D` below.  Since `Q` is an
   `OrbicurveFiniteEtaleCover X`, its structure map to `X` is finite etale by
   the cover type; what is missing is the construction of `Q` and of its
   universal property.  The trivial action is solved unconditionally, and the
   terminal-cover action is solved from the identity-finite-etale input;
   neither covers a nontrivial action on a nonterminal cover.  The tree
   contains the *definition* `Iut.OrbicurveSignQuotientWitness` for the
   quotient of a base orbicurve by its sign action, but no construction of any
   inhabitant of that structure, and that structure is a different quotient
   (of the base, not of a cover).  Consequently it is not a constructor of
   `S1763QuotientCoverRequired`.
2. **Mono direct summand.**  For a mono `i : A ⟶ B` whose domain is not
   initial, the required datum is an actual complement cover `Z` and a
   colimiting binary cofan `(i, u : Z ⟶ B)`.  This is
   `S1763MonoComplementRequired i` below.  The scheme-cover proof of the
   project (`Example36CurveGaloisCategory`) uses a clopen complement of the
   image in a topological space; no such clopen-space API is provided for
   etale stacks in the present tree, so that proof is not available here.

No `sorry`, no new axiom, and no fake inhabitant of either missing proposition
is introduced.  The only axioms of the constructed declarations are expected
to be `propext`, `Classical.choice`, and `Quot.sound`; this is checked at the
end of the file.
-/

import tmp.sheaf.xif.paper.S1736CoverGaloisCategoryActual
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual

open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1736CoverGaloisCategoryActual

universe u

/-! ## 0. Generic categorical facts

These facts are independent of the orbicurve.  They are the part of the two
obligations that can be settled without new geometry. -/

section Generic

/-- `SingleObj G` is a connected category: it has one object, and every
functor from it to a discrete category is constant.  This is the index
category of a group action in `PreGaloisCategory`. -/
instance singleObj_isConnected (G : Type u) [Group G] : IsConnected (SingleObj G) where
  toIsPreconnected := inferInstance
  is_nonempty := ⟨SingleObj.star G⟩

/-- The colimit of the trivial action: for any connected index category and
any object `A`, the constant diagram at `A` has colimit `A`. -/
theorem hasColimit_const_singleObj
    {C : Type u} [Category.{u} C] {G : Type u} [Group G] (A : C) :
    HasColimit ((Functor.const (SingleObj G)).obj A) :=
  inferInstance

/-- **The initial-domain case of the mono/direct-summand axiom.**
If `A` is initial, then any mono `i : A ⟶ B` is the first leg of a binary
coproduct with complement `B` and second leg `𝟙 B`.  The key point is that
maps out of an initial object are unique, so the lower triangle of any cocone
is automatically compatible.  No mono hypothesis is needed for the colimit
construction beyond the statement's own `Mono i` binder. -/
theorem monoDirectSummand_of_initial_domain
    {C : Type u} [Category.{u} C] {A B : C}
    (hA : IsInitial A) (i : A ⟶ B) [Mono i] :
    ∃ (Z : C) (u : Z ⟶ B), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  refine ⟨B, 𝟙 B, ⟨?_⟩⟩
  refine BinaryCofan.IsColimit.mk (s := BinaryCofan.mk i (𝟙 B))
    (fun {T} f g => g) ?_ ?_ ?_
  · intro T f g
    rw [BinaryCofan.mk_inl]
    exact IsInitial.hom_ext hA (i ≫ g) f
  · intro T f g
    rw [BinaryCofan.mk_inr]
    exact Category.id_comp g
  · intro T f g m hm1 hm2
    rw [BinaryCofan.mk_inr] at hm2
    have hm2' : (𝟙 B) ≫ (show B ⟶ T from m) = g := hm2
    change (show B ⟶ T from m) = g
    simpa using hm2'

/-- The cocone of a diagram whose object is a terminal object `T`: every
object of the diagram maps to `T` by the unique map to the terminal object. -/
def terminalCocone
    {C : Type u} [Category.{u} C] {G : Type u} [Group G]
    (D : SingleObj G ⥤ C) (T : C) (hT : IsTerminal T)
    (hobj : ∀ j, D.obj j = T) : Cocone D where
  pt := T
  ι :=
    { app := fun j => hT.from (D.obj j)
      naturality := by
        intro j j' f
        exact hT.hom_ext _ _ }

/-- The terminal-action cocone is colimiting.  The key point is that the
diagram object is the terminal object, so the only possible cocone point is
again reached through the unique leg of the cocone at the single object. -/
def isColimitTerminalCocone
    {C : Type u} [Category.{u} C] {G : Type u} [Group G]
    (D : SingleObj G ⥤ C) (T : C) (hT : IsTerminal T)
    (hobj : ∀ j, D.obj j = T) :
    IsColimit (terminalCocone D T hT hobj) where
  desc s := eqToHom (hobj (SingleObj.star G)).symm ≫ s.ι.app (SingleObj.star G)
  fac s j := by
    have hj : j = SingleObj.star G := Quiver.SingleObj.ext
    subst hj
    cases hobj (SingleObj.star G)
    simp [terminalCocone]
  uniq s m hm := by
    have h := hm (SingleObj.star G)
    cases hobj (SingleObj.star G)
    simp [terminalCocone] at h ⊢
    exact h

/-- Any action whose object is a terminal object has a colimit, namely the
terminal object itself. -/
theorem hasColimit_of_terminal_action
    {C : Type u} [Category.{u} C] {G : Type u} [Group G]
    (D : SingleObj G ⥤ C) (T : C) (hT : IsTerminal T)
    (hobj : ∀ j, D.obj j = T) : HasColimit D :=
  ⟨terminalCocone D T hT hobj, isColimitTerminalCocone D T hT hobj⟩

end Generic

/-! ## 1. The actual S1728 category and the two exact data -/

section Actual

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

/-- The actual category structure of S1728, used locally so that the
statements below can be written with the ordinary `⟶` notation.  This is
not a new category: it is literally `S1728CoverCategory11`. -/
local instance s1763ActualCategory :
    Category.{u + 1, u + 1} (OrbicurveFiniteEtaleCover X) :=
  S1728CoverCategory11 (F := F) (X := X)

/-- The actual cover type of the S1728 category. -/
abbrev S1763Cover := OrbicurveFiniteEtaleCover X

/-- The quotient-by-finite-groups obligation, written in the exact
colimit-cocone form.  This is a restatement of the literal S1736 field, not a
weakening: `S1763FiniteGroupQuotientData_iff` proves the equivalence. -/
def S1763FiniteGroupQuotientData
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Prop :=
  ∀ (G : Type (u + 1)) [Group G] [Finite G]
    (D : SingleObj G ⥤ OrbicurveFiniteEtaleCover X),
    Nonempty (ColimitCocone D)

/-- The exact per-diagram quotient requirement: an actual cover together with
a colimiting cocone.  The quotient object is a member of
`OrbicurveFiniteEtaleCover X`, so its structure map to `X` is finite etale by
the cover type; the missing work is the construction of this object and of its
universal property.  For a nontrivial action this is the first missing
geometric datum of the quotient field. -/
def S1763QuotientCoverRequired
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (G : Type (u + 1)) [Group G] [Finite G]
    (D : SingleObj G ⥤ OrbicurveFiniteEtaleCover X) : Prop :=
  Nonempty (ColimitCocone D)

/-- The mono/direct-summand obligation, written as the exact existence of a
complement cover and a binary coproduct colimit.  This is the literal S1736
field. -/
def S1763MonoDirectSummandData
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Prop :=
  ∀ {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B) [Mono i],
    ∃ (Z : OrbicurveFiniteEtaleCover X) (u : Z ⟶ B),
      Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The exact per-mono complement requirement.  For a mono whose domain is
not initial this is the first missing geometric datum of the mono field. -/
def S1763MonoComplementRequired
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B) [Mono i] : Prop :=
  ∃ (Z : OrbicurveFiniteEtaleCover X) (u : Z ⟶ B),
    Nonempty (IsColimit (BinaryCofan.mk i u))

/-- **Exact equivalence of the quotient data with the literal S1736 field.**
The forward direction chooses a colimiting cocone for every diagram, as
`HasColimitsOfShape` demands. -/
theorem S1763FiniteGroupQuotientData_iff
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) :
    S1763FiniteGroupQuotientData F X ↔
      S1736FiniteGroupQuotientObligation (F := F) (X := X) := by
  constructor
  · intro h G _ _
    exact { has_colimit := fun D => HasColimit.mk (Classical.choice (h G D)) }
  · intro h G _ _ D
    exact (h G).has_colimit D |>.exists_colimit

/-- **Exact equivalence of the mono data with the literal S1736 field.** -/
theorem S1763MonoDirectSummandData_iff
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) :
    S1763MonoDirectSummandData F X ↔
      S1736MonoDirectSummandObligation (F := F) (X := X) :=
  Iff.rfl

/-- The per-diagram requirement is exactly the local form of the global
quotient data. -/
theorem S1763FiniteGroupQuotientData_iff_forall
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) :
    S1763FiniteGroupQuotientData F X ↔
      ∀ (G : Type (u + 1)) [Group G] [Finite G]
        (D : SingleObj G ⥤ OrbicurveFiniteEtaleCover X),
        S1763QuotientCoverRequired F X G D :=
  Iff.rfl

/-- The per-mono requirement is exactly the local form of the global mono
data. -/
theorem S1763MonoDirectSummandData_iff_forall
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) :
    S1763MonoDirectSummandData F X ↔
      ∀ {A B : OrbicurveFiniteEtaleCover X} (i : A ⟶ B) [Mono i],
        S1763MonoComplementRequired F X i :=
  Iff.rfl

/-! ## 2. The trivial action: a genuine quotient colimit

For the trivial action, the diagram is the constant diagram at the cover
`A`, and its colimit is `A` itself.  This is a full construction of one
nontrivial part of the quotient field (the group may be any finite group; only
the action is trivial). -/

/-- The trivial action of any finite group on a cover has a colimit, namely
the cover itself. -/
theorem S1763TrivialActionQuotient
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (G : Type (u + 1)) [Group G] [Finite G]
    (A : OrbicurveFiniteEtaleCover X) :
    Nonempty (ColimitCocone ((Functor.const (SingleObj G)).obj A)) :=
  (hasColimit_const_singleObj
    (C := OrbicurveFiniteEtaleCover X) (G := G) A).exists_colimit

/-- The explicit colimiting cocone of the trivial action: point `A`, all
legs identities.  This is `Limits.isColimitConstCocone` at the connected
index category `SingleObj G`. -/
def S1763TrivialActionQuotientCocone
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (G : Type (u + 1)) [Group G] [Finite G]
    (A : OrbicurveFiniteEtaleCover X) :
    IsColimit (Limits.constCocone (SingleObj G) A) :=
  Limits.isColimitConstCocone (SingleObj G) A

/-- The point of the trivial-action colimit is the original cover. -/
theorem S1763TrivialActionQuotient_point
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (G : Type (u + 1)) [Group G] [Finite G]
    (A : OrbicurveFiniteEtaleCover X) :
    (Limits.constCocone (SingleObj G) A).pt = A :=
  rfl

/-- Conditional quotient for an action on the terminal cover.  The hypothesis
`h` is exactly S1736's missing identity-finite-etale datum: it makes the
identity cover terminal.  Once it is supplied, every action whose object is
that terminal cover has a colimit, namely the terminal cover. -/
theorem S1763TerminalActionQuotient
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (G : Type (u + 1)) [Group G] [Finite G]
    (D : SingleObj G ⥤ OrbicurveFiniteEtaleCover X)
    (hobj : ∀ j, D.obj j = S1736TerminalCover (F := F) (X := X) h) :
    Nonempty (ColimitCocone D) :=
  (hasColimit_of_terminal_action D
    (S1736TerminalCover (F := F) (X := X) h)
    (S1736TerminalCover_isTerminal (F := F) (X := X) h)
    hobj).exists_colimit

/-! ## 3. The initial-domain case of the mono field

This is the only case of the mono field settled unconditionally here.  It is a
real construction on the actual category, but it applies only to monos whose
domain is an initial cover.  The actual cover category's initial object is not
constructed in the tree, so this does not discharge the global field. -/

/-- The initial-domain case specialised to the actual S1728 cover category. -/
theorem S1763MonoSplitting_at_initial
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (I : OrbicurveFiniteEtaleCover X) (hI : IsInitial I)
    {B : OrbicurveFiniteEtaleCover X} (i : I ⟶ B) [Mono i] :
    S1763MonoComplementRequired F X i :=
  monoDirectSummand_of_initial_domain
    (C := OrbicurveFiniteEtaleCover X) hI i

/-- Exact missing initial-cover datum: an initial object of the actual cover
category.  If it were supplied, the initial-domain case above would apply to
it, but the global mono field would still require the complement for every
other domain. -/
def S1763InitialCoverRequired
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Prop :=
  Nonempty (Σ I : OrbicurveFiniteEtaleCover X, IsInitial I)

/-! ## 4. The sign quotient interface is not a constructor

`Iut.OrbicurveSignQuotientWitness` is the bicategorical universal property of
the quotient of the base orbicurve by its sign action.  It is a structure with
only fields; the tree contains no constructor and no inhabitant.  It is also a
different quotient from `S1763QuotientCoverRequired`: the latter quotients a
cover `A` over `X` by a finite group acting on `A`, whereas the sign witness
quotients the base `X` itself.  We record its exact missing form so that no
later consumer mistakes the definition for a construction. -/

/-- The sign-action datum itself is a structure, not a theorem. -/
abbrev S1763SignActionRequired
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Type (u + 1) :=
  Iut.OrbicurveSignAction X

/-- The full missing sign-quotient package: an action, a quotient orbicurve,
the invariant quotient map, and the bicategorical universal property. -/
abbrev S1763SignQuotientWitnessRequired
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Type (u + 1) :=
  Σ (action : Iut.OrbicurveSignAction X)
    (C : Iut.HyperbolicOrbicurve F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

/-- The exact missing proposition.  No inhabitant is asserted. -/
def S1763SignQuotientMissing
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F) : Prop :=
  Nonempty (S1763SignQuotientWitnessRequired F X)

/-- The sign-quotient witness has a `descend` field for every invariant map.
This projection is recorded only to show the shape of the missing data; it is
not a construction of the witness. -/
def S1763SignQuotientWitness_descend
    (F : Type u) [Field F] {X C : HyperbolicOrbicurve F}
    {action : Iut.OrbicurveSignAction X}
    {quotient : Iut.OrbicurveSignInvariantMorphism action C}
    (w : Iut.OrbicurveSignQuotientWitness action quotient)
    (Y : Iut.HyperbolicOrbicurve F)
    (invariant : Iut.OrbicurveSignInvariantMorphism action Y) :
    C.Hom Y :=
  w.descend Y invariant

/-! ## 5. Assembly: the two data plug into the literal S1736 fields

This is the consumer check.  The theorem takes the exact quotient and mono
data together with the three other S1736 inputs and produces the actual
`S1736ActualPreGaloisObligation`.  It constructs no quotient and no
complement. -/

/-- Assembly of the actual S1736 PreGalois obligation from the five exact
inputs: identity finite-etale, pullbacks, finite coproducts, the quotient data,
and the mono data. -/
theorem S1763PreGaloisCategoryOfInputs
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (hTerm : S1736IdentityFiniteEtale (F := F) (X := X))
    (hPull : S1736PullbackObligation (F := F) (X := X))
    (hCoprod : S1736FiniteCoproductObligation (F := F) (X := X))
    (hQuot : S1763FiniteGroupQuotientData F X)
    (hMono : S1763MonoDirectSummandData F X) :
    S1736ActualPreGaloisObligation (F := F) (X := X) := by
  apply S1736PreGaloisCategoryOfInputs hTerm hPull hCoprod ?_ ?_
  · intro G _ _
    exact { has_colimit := fun D => HasColimit.mk (Classical.choice (hQuot G D)) }
  · exact fun {A B} (i : A ⟶ B) (_ : Mono i) => hMono i

/-- The same assembly, but consuming the literal S1736 fields directly.
This records that the two data are not weaker than the fields they replace. -/
theorem S1763PreGaloisCategoryOfLiteralInputs
    (F : Type u) [Field F] (X : HyperbolicOrbicurve F)
    (hTerm : S1736IdentityFiniteEtale (F := F) (X := X))
    (hPull : S1736PullbackObligation (F := F) (X := X))
    (hCoprod : S1736FiniteCoproductObligation (F := F) (X := X))
    (hQuot : S1736FiniteGroupQuotientObligation (F := F) (X := X))
    (hMono : S1736MonoDirectSummandObligation (F := F) (X := X)) :
    S1736ActualPreGaloisObligation (F := F) (X := X) :=
  S1736PreGaloisCategoryOfInputs hTerm hPull hCoprod hQuot hMono

/-! ## 6. Status markers and axiom audit -/

#check S1763FiniteGroupQuotientData
#check S1763QuotientCoverRequired
#check S1763MonoDirectSummandData
#check S1763MonoComplementRequired
#check S1763FiniteGroupQuotientData_iff
#check S1763MonoDirectSummandData_iff
#check S1763TrivialActionQuotient
#check S1763TrivialActionQuotientCocone
#check terminalCocone
#check isColimitTerminalCocone
#check hasColimit_of_terminal_action
#check S1763TerminalActionQuotient
#check S1763MonoSplitting_at_initial
#check S1763InitialCoverRequired
#check S1763SignActionRequired
#check S1763SignQuotientWitnessRequired
#check S1763SignQuotientMissing
#check S1763PreGaloisCategoryOfInputs
#check S1763PreGaloisCategoryOfLiteralInputs

#print axioms singleObj_isConnected
#print axioms hasColimit_const_singleObj
#print axioms monoDirectSummand_of_initial_domain
#print axioms S1763FiniteGroupQuotientData_iff
#print axioms S1763MonoDirectSummandData_iff
#print axioms S1763TrivialActionQuotient
#print axioms S1763TrivialActionQuotientCocone
#print axioms terminalCocone
#print axioms isColimitTerminalCocone
#print axioms hasColimit_of_terminal_action
#print axioms S1763TerminalActionQuotient
#print axioms S1763MonoSplitting_at_initial
#print axioms S1763SignQuotientWitness_descend
#print axioms S1763PreGaloisCategoryOfInputs
#print axioms S1763PreGaloisCategoryOfLiteralInputs

end Actual

end LeanFormal.IUT.XiFPaper.S1763CoverQuotientsActual