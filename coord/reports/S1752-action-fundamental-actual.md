# S1752: the full finite-action category for the absolute Galois group

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1752ActionFundamentalActual.lean

EXIT=0

SHA256 (source): 082D459618F5E4653805F50C0EEB67B8D29C23F3384D4C204F86C98170FCE574

Source size: 28697 bytes.

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1752ActionFundamentalActual.olean (279912 bytes)

SHA256 (olean): 810BB0369EACEFB2B2C3E9F3BED83B8DF23C41763E1C8B5E9A55B8A09611356F

Checker: tmp/sheaf/xif/paper/S1752Check.lean, EXIT=0, SHA256
9530009AA7205159FB937EF7509178418A96A150A74A2D1F93401C54AF27E36E.

No sorry, no admit, no new axiom, no Shrink/ULift/PUnit, no fake group,
action or category.

## Status of S1751 and the literal target

S1751 is present in the tree:

- source: tmp/sheaf/xif/paper/S1751FiniteIndexOpenActual.lean,
  SHA256 264CED4DA61B7865B1F1E574D067262350690DC67C5817E0D93B3BA8EFBD09A8,
  15152 bytes;
- olean: .../S1751FiniteIndexOpenActual.olean,
  SHA256 193DC186F8A7A14D87106C0ECA41D8A05C090F28EB6ED29903D57E40BD9EDA91,
  84248 bytes.

S1751 formally proves:

- S1751Target F is definitionally S1737AbsoluteGaloisEveryFiniteIndexSubgroupOpen F;
- S1751Target F iff S1737AbsoluteGaloisActionForgetMissing F;
- S1751NonOpenSubgroupMissing F implies not S1751Target F;
- a non-open finite-index subgroup refutes the literal full-action
  IsFundamentalGroup statement.

It does NOT prove S1751NonOpenSubgroupMissing F.  The number-field
counterexample is cited from Milne, Fields and Galois Theory, Chapter 7,
Proposition 7.29; the Kummer-theoretic quotient and the choice construction of
a non-open finite-index subgroup are not formalized.  The file records that
input as a proposition, not an axiom.

Consequently the unconditional literal target

  PreGaloisCategory.IsFundamentalGroup
    (Action.forget FintypeCat.{0} (Iut.AbsoluteGaloisProfinite F))
    (Iut.AbsoluteGaloisProfinite F)

is not established.  By the cited Milne result (and S1751's reduction) it is
false for number fields, in particular for F = S1720Field.  The correct formal
result is the conditional theorem with the exact missing condition, plus the
refutation reduction under S1751's external input.

## Unconditional content

* S1752ActionGaloisCategoryCertificate and S1752ActionGaloisCategoryData:
  Action FintypeCat.{0} G is a Mathlib Galois category, and the forgetful
  functor is a fibre functor.  The data-carrying structure stores the actual
  category and functor.

* S1752ActionAutCertificate: the automorphism group Aut (Action.forget ...)
  is a fundamental group (S1741's FiberFundamentalGroupCertificate).  It lives
  in ProfiniteGrp.{1} and hence cannot fill EtaleFundamentalGroup's
  group : ProfiniteGrp.{0} field.

* S1752ActionForgetMissing_of_isSepClosed: for a separably closed field the
  absolute Galois group is trivial, so every finite action is continuous.
  This yields an unconditional IsFundamentalGroup and an unconditional
  EtaleFundamentalGroup (S1752ActionEtaleFundamentalGroup_of_isSepClosed).

* S1752ActionForgetMissing_of_finite: if the absolute Galois group is finite,
  S1737's finite case discharges the missing condition.  This yields an
  unconditional IsFundamentalGroup and EtaleFundamentalGroup.

## Conditional content and exact missing

The exact missing condition is

  S1752ActionForgetMissing F :=
    S1737AllFiniteActionsContinuous (Iut.AbsoluteGaloisProfinite F).

It is equivalent to:

* S1752EveryFiniteIndexSubgroupOpen F: every finite-index subgroup of G is
  open (S1752ActionForgetMissing_iff_everyFiniteIndexOpen);
* S1751Target F (S1752ActionForgetMissing_iff_S1751Target);
* the existence of a continuous group isomorphism
  e : G ≃ₜ* Aut (Action.forget FintypeCat.{0} G) whose action is the
  canonical evaluation action (S1752ActionForgetMissing_iff_exists_continuousMulEquiv).

Under S1752ActionForgetMissing F:

* S1752ActionForget_isFundamentalGroup proves the literal S1737 target;
* S1737ActionForget_isFundamentalGroup is the same statement under the exact
  requested name;
* S1752ActionForgetToAutContinuous constructs the continuous comparison with
  Aut and S1752ActionForgetToAutContinuous_smul identifies its action;
* S1752ActionEtaleFundamentalGroup packages a genuine Iut.EtaleFundamentalGroup
  with Cover = Action FintypeCat.{0} G, fiber = Action.forget FintypeCat.{0} G,
  group = G, and action = the actual Action.instMulAction.  Its
  isFundamentalGroup field is the conditional theorem.
  S1752ActionEtaleFundamentalGroup_certified reads the field back.

Additional conditional constructors:
S1752ActionEtaleFundamentalGroup_of_everyFiniteIndexOpen,
S1752ActionEtaleFundamentalGroup_of_S1751Target,
S1752ActionEtaleFundamentalGroup_of_continuousMulEquiv.

## Refutation shape

If S1751NonOpenSubgroupMissing F holds, then:

* not S1752ActionForgetMissing F
  (S1752ActionForgetMissing_false_of_S1751NonOpenSubgroupMissing);
* not IsFundamentalGroup (Action.forget ...) G
  (S1752ActionForget_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing);
* at F = S1720Field the same
  (S1752S1720_not_isFundamentalGroup_of_S1751NonOpenSubgroupMissing).

The external input itself is not asserted.

## Universe check

S1752ActionEtaleFundamentalGroup F h has

  Cover : Type 1,
  group : ProfiniteGrp.{0},

matching Iut.EtaleFundamentalGroup exactly (the category is Category.{0,1}).
The Aut certificate has group ProfiniteGrp.{1}; this is the precise universe
obstruction to using Aut in the EtaleFundamentalGroup.

## Axiom audit

#print axioms on all load-bearing declarations reports only

  propext, Classical.choice, Quot.sound.

There is no sorryAx and no other axiom.

## Verification commands

  lake env lean tmp/sheaf/xif/paper/S1752ActionFundamentalActual.lean
  -> EXIT=0

  lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1752ActionFundamentalActual.olean tmp/sheaf/xif/paper/S1752ActionFundamentalActual.lean
  -> EXIT=0

  lake env lean tmp/sheaf/xif/paper/S1752Check.lean
  -> EXIT=0

The checker rechecks all key declaration types, the Galois-category data
certificate, the conditional EtaleFundamentalGroup, the unconditional
separably closed and finite cases, and the axiom footprint.
