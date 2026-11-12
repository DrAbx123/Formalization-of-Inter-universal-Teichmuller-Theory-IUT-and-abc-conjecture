# S1762: actual cover category — identity cover finite etale; terminal field closed; exact pullback/coproduct missing

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1762CoverLimitsActual.lean

EXIT=0

SHA256: 7FB5845B6BE92BA26B3A81E14151F693F593A2B3DAD44F822460B07137EB2A97

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1762CoverLimitsActual.olean (114136 bytes)

olean SHA256: 70BF54C01ABEC5E3891E79EF54B3CF35343931FED59A875E064567536024F3C2

Import check: tmp/sheaf/xif/paper/S1762Check.lean imports the olean and reprints the axiom sets.

## Actual constructions

* S1762IdentityFiniteEtale: a genuine inhabitant of
  EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.id X.stack.fiber)
  for the actual S1726 orbicurve X = S1726Orbicurve.

  The base-change presentation at every scheme-valued point uses the test scheme
  itself as pullback, the identity as projection, the identity strong
  transformation as comparison map, and the right/left unitors as the
  commutation 2-isomorphism.  The two-pullback witness has lift = cone.toY,
  liftToX = cone.commutes.symm ≪≪ rightUnitor cone.toX, liftToY = rightUnitor
  cone.toY, and liftTwoCell = morphism.toY.

  The three coherence fields are equalities of 2-cells into the representable
  S1726 stack (X.stack.fiber = schemeRepresentableEtalePseudofunctor K
  S1726AffineOver, by S1726Orbicurve_stack_fiber), so they are subsingletons
  (S1762Modification_subsingleton_stack).  This is the only point where the
  construction uses the concrete S1726 orbicurve rather than an arbitrary
  hyperbolic orbicurve.

* S1762IdentityFiniteEtaleActual: S1736IdentityFiniteEtale for the actual
  S1726 orbicurve.  This closes the first of the six S1736 missing
  propositions.

* S1762TerminalCover / S1762TerminalCover_isTerminal: the identity cover is
  the actual terminal object of the S1728 2-isomorphism quotient category.

* S1762HasTerminalActual: HasTerminal on the actual S1736 category
  (Category.{1,1} on OrbicurveFiniteEtaleCover S1726Orbicurve).

* S1762HasTerminalS1728: HasTerminal stated directly on S1728ActualCategory11.

* S1762HasFiniteLimits_of_pullbacks: the finite-limit field now reduces to
  pullbacks alone; the terminal input is discharged.

* S1762PreGaloisCategoryOfRemainingInputs: the actual PreGaloisCategory
  assembles from the four remaining inputs (pullbacks, finite coproducts,
  finite-group quotients, mono/direct summand).  The terminal input is no
  longer an input.

## Exact remaining first missing

Not constructed, and recorded as exact propositions:

* S1762PullbackObligationActual = S1736PullbackObligation for S1726:
  literally HasPullbacks on the actual S1728 category.
  Geometric content: the bicategorical fibre product of the two cover source
  stacks over the common cover, a two-pullback witness for its defining square,
  finite etaleness of the two projections, and the induced universal property in
  the 2-isomorphism quotient.

* S1762FiniteCoproductObligationActual = S1736FiniteCoproductObligation for
  S1726: literally HasFiniteCoproducts on the actual S1728 category.
  Geometric content: the disjoint union stack of the two cover source stacks
  over the base, finite etaleness of the two inclusions, the initial object, and
  the induced coproduct universal property in the 2-isomorphism quotient.

* S1762FiniteGroupQuotientObligationActual and
  S1762MonoDirectSummandObligationActual: the remaining two PreGalois fields,
  recorded exactly.

* S1762FiberFunctorObligationActual: the exact fiber-functor obligation on the
  actual Category.{1,1}.

The two-pullback witness alone is not enough for the quotient-category limit;
the quotient universal property is a separate missing half.

## Axiom audit

#print axioms reports only propext, Classical.choice and Quot.sound for:
S1762Modification_subsingleton_stack, S1762IdentityFiniteEtale,
S1762IdentityFiniteEtaleActual, S1762TerminalCover_isTerminal,
S1762HasTerminalActual, S1762HasTerminalS1728,
S1762HasFiniteLimits_of_pullbacks and
S1762PreGaloisCategoryOfRemainingInputs.

There is no sorry, no axiom declaration, no Shrink, no ULift, no PLift and no
PUnit in the code.  The word Shrink/ULift appears only in the honest-boundary
docstring.

## Environment note

The workspace had heavy concurrent Lean activity during this task.  Several
one-shot compiles failed with transient 'failed to read file ...olean' errors on
unrelated Mathlib/core modules; the final compile succeeded on retry
(EXIT=0) and an independent import check of the produced olean also succeeded.
No dependency module was modified by this task.
