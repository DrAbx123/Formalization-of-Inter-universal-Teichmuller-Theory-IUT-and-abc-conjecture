# S1994: the K-side covers -- underlying isogeny kernel, label vacuity, and the exact first missing

Date: 2026-11-01 (Asia/Shanghai)
Workspace: D:\lean
Source: tmp/sheaf/xif/paper/S1994KSideCoversActual.lean
OLean: .lake/build/lib/lean/tmp/sheaf/xif/paper/S1994KSideCoversActual.olean
Status: EXIT=0. Production definitions unchanged. No axiom, sorry, admit or
arbitrary carrier. The actual degree-l finite-etale cover is NOT constructed;
the exact first missing below is machine-checked as a decomposition and as an
obstruction.

## The task

S1989 specified the paper-faithful K-side cover record KSideCoverActual
(actual X_K^-> -> X_K and C_K^-> -> C_K of degree l, the quotient
X_K^-> -> C_K^->, and the 2-commutative quotient square) and proved that no
inhabitant exists. S1994 was asked either to construct the actual covers
(including the underlying isogeny E_K^-> -> E_K and the rank-one quotient
geometry) or to pin down the exact first missing. No fake cover is used.

## Verdict

The construction is blocked, and S1994 pins the block precisely:

* The curve-level half is constructed up to the isogeny kernel: the actual
  K-side curve A.curve.baseChange A.K, the rank-one quotient of IUT I
  Definition 3.1(c), and the kernel line H of the degree-l isogeny, with
  exactly l elements.
* The stack-level half is not constructed, and the only orbicurve
  construction present in the tree (representable etale stacks) is proved
  unable to supply it: representable stacks have discrete fibers, hence no
  stacky point of any order, while the paper's l-tors orbicurve has an order-l
  stacky point. This is a theorem, not a failure to find a proof.
* The S1989 record's label fields are vacuous: the record is equivalent to
  its label-free form, and any two orbicurves with any finite-etale degree-l
  maps to the cores give the labelled record after relabelling. Hence the
  S1989 record alone is not the paper's cover.

## What is constructed

Curve level, from production data only:

* S1994KCurve l A = A.curve.baseChange A.K, with the rfl lemmas
  S1994KCurve_curve and S1994KCurve_base.
* S1994RankOneQuotient B : TorsionRankOneQuotientData l (S1994KCurve l A),
  for any K-side torsion basis B (source type S1994TorsionBasis l A).
* S1994KernelLine B: the kernel of the rank-one quotient map, i.e. the kernel
  of the underlying degree-l isogeny E_K^-> -> E_K.
* S1994KernelLine_eq_span: the kernel is exactly the line spanned by
  S1994KernelVector B (the second basis vector), and
  S1994KernelVector_ne_zero: that generator is nonzero.
* S1994KernelLine_card: Nat.card of the kernel line is l.
* S1994KernelEquiv: the kernel line is (as a type) the coefficient ring
  ZMod l.
* S1994rankOneQuotient_is_rank_one and
  S1994rankOneQuotient_distinguished: the quotient is rank one, and the
  distinguished class is nonzero and reads as 1 under the quotient
  equivalence.
* S1994IsogenyKernelDatum: the curve-level isogeny-kernel datum (line, l
  elements, single nonzero generator).
* S1994IsogenyKernelDatumOfClauseC: the datum obtained from production clause
  (c) via SourceClauseC.k_torsion_basis; S1994IsogenyKernelDatumOfClauseC_card
  records the l-element kernel.

Not constructed: the quotient curve E_K^-> = E_K / H and the isogeny itself.
Mathlib has no isogeny theory for Weierstrass curves, no quotient by a finite
subgroup, and no l-tors theta/Kummer cover of a punctured elliptic curve.

## What is proved about the S1989 record

Label vacuity. Iut.HyperbolicOrbicurve.Hom only sees stack.fiber, the
finite-etale certificate only sees the two fibers and the map, and the degree
predicate only sees the certificate and the target fiber. The transports

* S1994Relabel (and S1994RelabelStack), S1994RelabelHom,
* S1994TransportPresentation{,Source}, S1994TransportFiniteEtale{,Source},
* S1994TransportDegree{,Source}

rebuild every certificate and degree statement at the relabelled stack
records. Consequently:

* KSideCoverUnlabelled: the S1989 record with the two signature fields deleted.
* KSideCoverUnlabelled.ofLabelled / .toLabelled: both directions.
* S1994KSideCoverActual_iff_unlabelled:
    Nonempty (KSideCoverActual l A S C) <-> Nonempty (KSideCoverUnlabelled l A S C).
* S1994labelledRecord_of_arbitrary_endpoints: *arbitrary* orbicurves X, Y, an
  arbitrary finite-etale degree-l map to each core, an arbitrary finite-etale
  quotient map and an arbitrary 2-commutative square already give the labelled
  S1989 record.

Representable orbicurves. S1994RepresentableIsStack: every representable
etale pseudofunctor over F is an etale stack (S1419's discrete-sheaf descent
bridge, applied to the representable sheaf). S1994RepresentableOrbicurve: the
realised orbicurve with an arbitrary hyperbolic signature.
S1994RepresentableOrbicurve_aut_eq_id: every automorphism of every point is
the identity. Hence S1994RepresentableOrbicurve_noAut and
S1994RepresentableOrbicurve_noAutOfOrder: no stacky point of any order.

S1994Point / S1994HasNontrivialAut / S1994HasAutOfOrder: the point-level
formalisation of a stacky point (a U-point with a nontrivial automorphism; of
exact order n).

The label-only orbicurve. S1994LabelOnlyLTorsOrbicurve: an actual orbicurve
over A.K whose signature is exactly (1,l-tors), built as the representable
stack of Spec K. It has trivial automorphism groups
(S1994LabelOnlyLTorsOrbicurve_noAut,
S1994LabelOnlyLTorsOrbicurve_noAutOfOrder), so it is not the l-tors orbifold.
S1994label_does_not_force_stackiness records this dichotomy: the label exists,
the order-l stacky point is missing.

## The paper-faithful datum and the exact first missing

S1994PaperKSideCover: the S1989 record plus the honest stacky-point geometry
(order l on X_K^->, orders 2 and l on C_K^->). S1994PaperKSideCoverMissing is
the target; S1994FirstMissing is the same over the production core
S1984PaperKCore.ofSource E.

Machine-checked decomposition:

* S1994paperKSideCoverMissing_iff: the paper cover is exactly the S1989 record
  plus the three stacky-point conditions.
* S1994firstMissing_iff: the same over the production core.
* S1994firstMissing_implies_record: the first missing implies the S1989 cover
  record.
* S1994firstMissing_implies_stacky: the first missing implies
  S1994StackyOrbicurveMissing l A, i.e. an actual orbicurve over A.K with an
  order-l stacky point.
* S1994PaperKSideCover.xArrow_not_representable: the paper cover's X_K^->
  cannot be any representable orbicurve.
* S1994production_conclusion: consumer entry point over the production core
  (the implication above plus the label-vacuity equivalence).
* S1994representable_no_stacky_summary: the representable obstruction in one
  statement.

Exact first missing, in dependency order:

1. S1994StackyOrbicurveMissing l A: an actual orbicurve over A.K with a point
   whose automorphism has order l; equivalently an actual non-representable
   etale stack over A.K (the l-tors root stack / stackification at the
   origin). The tree has IsStack only for representable (discrete) fibers
   (S1419); the action-category colimit is only pointwise (S1971); the
   general quotient-stack route is S1964's open G1. S1994 proves that the
   representable route cannot supply it.
2. Nonempty (KSideCoverUnlabelled l A S C): actual finite-etale degree-l stack
   morphisms to the two K-cores with a 2-commutative square. Their base-change
   presentations require the two-pullback witnesses of S1891/S1892; those
   pasting/closure inputs are recorded as missing there.
3. The curve-level isogeny E_K^-> -> E_K with kernel the constructed line, and
   the identification of the l-tors cover with it. Only the kernel datum is
   constructed.

Consequence for the paper route: the S1989 K-side cover record is exactly its
label-free form and does not encode the l-tors geometry; a paper-faithful
statement must include the stacky-point conditions, and the first missing
object is a non-representable l-tors orbifold over A.K with its finite-etale
degree-l maps to the two K-cores.

## Verification

- Build: lake env lean -j1 -R D:\lean
    -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1994KSideCoversActual.olean
    tmp/sheaf/xif/paper/S1994KSideCoversActual.lean, EXIT=0.
- Compile log: tmp/sheaf/xif/paper/S1994_compile.log
  - 0 errors, 0 warnings, 0 sorryAx; 17 #print axioms blocks, only
    propext, Classical.choice, Quot.sound.
  - SHA256 E1F49389DBB01962937FDBFD7B2E0C079BCAC67FB0EB115DC66FEE8E1DBE9019.
- Import check: tmp/sheaf/xif/paper/_S1994ConsumerCheck.lean
  - log tmp/sheaf/xif/paper/S1994_olean_check.log, CHECK_EXIT=0.
- Source: 43311 bytes, 898 lines,
  - 35 theorems, 24 defs, 3 structures, 3 abbrevs, 0 axiom declarations.
  - SHA256 8E8695D6072EFC79F5E560ED8F9FE43D73CCDED5C6059AA60C3DB2CACD82676D.
- OLean: 927048 bytes,
  - SHA256 A491AEC4FC9C0CFF6CDC880BB825EB514C27CE4E7C44183E63D5C693BF7EDFE2.
- The only source occurrence of the words sorry and admit is the honesty
  paragraph of the module docstring; there is no sorry tactic and no axiom
  declaration.
- Not run: full Project build, comparator, independent review.

## Honest boundary

* No production definition is edited.
* The isogeny E_K^-> -> E_K and the l-tors cover are not constructed; only the
  kernel line (with its l elements and rank-one quotient) is.
* No quotient stack, root stack, stackification or non-representable IsStack
  instance is postulated.
* The survey statement that representable stacks are the only orbicurve
  construction used by S1419/S1726/S1886 is documented in the module docstring;
  it is not a formal exhaustiveness theorem.
