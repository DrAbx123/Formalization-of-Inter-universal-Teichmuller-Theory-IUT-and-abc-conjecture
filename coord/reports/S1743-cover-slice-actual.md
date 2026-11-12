# S1743: actual cover category vs the S1733 affine finite-etale slice

Layer: D6 orbicurve cover category / finite-etale slice comparison.
Source objects: S1728 cover category (2-isomorphism-quotient homs,
S1728ActualCategory11), S1733 affine finite-etale slice
(P.CostructuredArrow ⊤ Scheme.Spec (Spec R') with P = IsFinite inf Etale),
S1733Model / S1733ModelOver, S1742 2-Yoneda comparison.
Reused results: S1728 (cover category), S1733 (slice, model, conditional
EssentiallySmall/Category.{0,1}), S1742 (both directions of the 2-Yoneda
comparison for representable etale pseudofunctors).
No Shrink, ULift, PLift or PUnit; no new axiom; no fake category.

## Question

Is the actual finite-etale cover category of the S1726 D6 orbicurve, with homs
the 2-isomorphism classes of actual cover maps, equivalent (or category
equivalent) to the S1733 essentially small affine finite-etale slice?

## Built (actual, unconditional)

File: tmp/sheaf/xif/paper/S1743CoverSliceActual.lean (503 lines, 25656 bytes),
namespace LeanFormal.IUT.XiFPaper.S1743CoverSliceActual.

1. Object map.
   - S1743BaseChange A: the identity-point base-change presentation of a cover
     (S1733's presentation, projectionMap/commutes/isPullback included).
   - S1743Model_isAffine A: the model scheme is affine (IsFinite + affine base).
   - S1743ModelRing A = Spec of Γ(model A), S1743ModelHom A = the finite-etale
     structure morphism written from Spec Γ(model A).
   - S1743ModelHom_finiteEtale A: that morphism is finite and etale.
   - S1743Object : S1728Cover -> S1733Slice, with the computation rules
     S1743Object_left (the underlying ring) and S1743Object_hom (the structure
     morphism).  So the intended object-level comparison is *constructed*, using
     exactly S1733's model; no new model is chosen.

2. Half of item (a) (stack representability of a cover by its affine model).
   - S1743Square A: the two-commutative square of the identity-point base change.
   - S1743IdentityCone A: the identity cone (cover maps to itself and to the
     base by its own structure map; the comparison 2-cell is the unitor).
   - S1743Lift A: the lift given by the two-pullback universal property.
   - S1743ModelSection A: vcomp (S1743Lift A) toSource is 2-isomorphic to the
     identity of the cover source stack.
   - S1743Lift_projection A: the lift is compatible with the projections to the
     base (2-isomorphic to A.map).
   These are proved unconditionally from TwoPullbackWitness.lift/liftToX/liftToY.

3. Item (c) closed (reusing S1742).
   - S1743YonedaEval: evaluation at the identity section; S1743YonedaEval_eq_S1742
     identifies it definitionally with S1742HomOfStrongTrans.
   - S1743SchemeRepresentableMap f: the structure SchemeRepresentableMap, which
     S1726/S1733 use as an *assumption* in every EtaleStackBaseChangePresentation,
     is *constructed* for every scheme morphism f (from S1742StrongTransOfHom,
     whose components are exactly the required postcomposition functors).
   - S1743YonedaEval_app: every component of a representable strong
     transformation is postcomposition with its evaluation (S1742Key).
   - S1743YonedaEval_congr / _congr_iso: modifications, hence 2-isomorphisms, do
     not change the evaluation (discreteness of the components).
   - S1743YonedaEval_vcomp: evaluation is compatible with vertical composition.
   - S1743YonedaFunctor S T: strong transformations of representable stacks ->
     the *discrete* category of scheme morphisms S ⟶ T.
   - S1743YonedaClassMap / S1743YonedaClassEquiv: the 2-isomorphism classes of
     such transformations are *equivalent as a type* to the scheme morphisms
     S ⟶ T; both round trips are proved (S1742HomOfStrongTrans_strongTransOfHom
     and S1742StrongTransIsoOfHom).
   - S1743YonedaEssSurj: essential surjectivity of the evaluation functor.
   Consequence: the "CoverMap <-> scheme morphisms" obstruction of S1733 is
   removed at the representable level.  No smallness obstruction remains there.

4. The exact missing comparison, and its equivalence with S1733's target.
   - S1743CoverSliceComparison: a functor S1728Cover ⤍ S1733Slice whose object
     map is S1743Object up to isomorphism, which is fully faithful and
     essentially surjective.  No inhabitant is asserted.
   - S1743CoverSliceComparisonMissing, S1743SliceFunctorMissing: the
     propositional forms (the second drops the object-map identification).
   - S1743IsEquivalence_of + S1743SliceFunctorMissing_iff: a fully faithful
     essentially surjective functor is *exactly* S1733's
     S1733CoverSliceEquivalence (Nonempty Equivalence).  So the missing statement
     is not weakened relative to S1733.
   - S1743CoverSliceEquivalence_of_comparison, S1743EssentiallySmall_of_comparison,
     S1743Category01_of_comparison: the missing comparison yields S1733's slice
     equivalence, EssentiallySmall.{0} S1728Cover, and a genuine
     Category.{0,1} on the actual cover type (through S1733's conditional
     theorems; no new smallness input is invented).
   - S1743Object_injective_on_data, S1743Object_isAffineModel: what the object
     map gives on its own.

## Exact missing

(a) S1743SourceRetraction: for every cover A, a strong transformation
    A.source ⟹ Y (S1733Model A) whose composite with toSource is 2-isomorphic to
    the identity of the representable model.  The opposite composite is proved
    (S1743ModelSection).  This is not a consequence of item (c): toSource and its
    lift have a non-representable *source*, so the 2-Yoneda equivalence cannot
    see them.  Formally it is a statement about the two-pullback square: the
    recorded TwoPullbackWitness supplies lift, liftToX, liftToY, liftTwoCell and
    twoCell_ext (extensionality of 2-cells), but no inverse 2-cell and no
    one-cell uniqueness, so the retraction half is genuinely absent.

(b) S1743SliceFunctorMissing (equivalently S1743CoverSliceComparisonMissing):
    the comparison functor with fully faithful and essentially surjective
    proofs, i.e. cover maps modulo 2-isomorphism must be exactly the scheme
    morphisms between the affine models.  S1733's S1733CoverSliceEquivalence is
    *formally equivalent* to this (S1743SliceFunctorMissing_iff), so nothing is
    lost by the reformulation, and the object map is already fixed by
    S1743Object.  Even granting (a), (b) needs the transport of (c) across the
    model comparison, because S1728 cover maps are strong transformations
    between arbitrary (non-representable) stacks.

Explicitly not done: no functor S1728Cover ⤍ S1733Slice is constructed, no
full/faithful/ess-surjective proof is claimed, and no equivalence is asserted.

## Evidence

- Lean: tmp/sheaf/xif/paper/S1743CoverSliceActual.lean (503 lines, 25656 bytes)
- command: lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1743CoverSliceActual.olean tmp/sheaf/xif/paper/S1743CoverSliceActual.lean
- EXIT=0 (no errors, no warnings)
- source SHA256 64E687F9F6C31583DD0A6D09AE73B848B5E21FCC5D888387A9489982711CE83F
- olean .lake/build/lib/lean/tmp/sheaf/xif/paper/S1743CoverSliceActual.olean
  (235728 bytes), SHA256
  8E9B1F836494251DBEA42DBF54CEB3641ED7AA1B937B2269A576DFDE3D1245D8
- axiom audit (in-file #print axioms): S1743Model_isAffine, S1743ModelHom_finiteEtale,
  S1743Object, S1743ModelSection, S1743Lift_projection,
  S1743SchemeRepresentableMap, S1743YonedaEval_app, S1743YonedaEval_congr,
  S1743YonedaEval_vcomp, S1743YonedaEssSurj, S1743YonedaClassEquiv,
  S1743SliceFunctorMissing_iff, S1743EssentiallySmall_of_comparison,
  S1743Category01_of_comparison all depend only on propext, Classical.choice,
  Quot.sound.  No sorryAx, no axiom declaration, no Shrink/ULift/PUnit.
- scratch probe files created during this package were deleted; only the module
  above remains.

## Statement / closure status

statement_compiles = yes (target types written out with the actual
Iut.schemeRepresentableEtalePseudofunctor, S1733Slice, S1728Cover,
S1733CoverSliceEquivalence).
proof_body_checked = yes for the items listed under "Built".
kernel_closed = yes for those items (axiom trio only).
target_accepted = false: the equivalence S1728Cover ≃ S1733Slice is NOT
constructed; (a) and (b) above are the exact remaining gaps.

## Consumer

S1733's first-missing interface S1733CoverSliceEquivalence and its downstream
S1733EssentiallySmall_of_sliceMissing / S1733Category01_of_sliceMissing, hence
the G6 field of S1732's SourceDefinition31Data (OrbicurveFundamentalGroupData /
small Galois cover category).  The package removes one of S1733's three named
gaps outright (the 2-Yoneda comparison), constructs the object map and half of
the stack representability, and reduces the rest to (a)+(b) in a form that is
formally equivalent to S1733's own target.

## Next executable step

Prove (a) for one cover, then for all: strengthen the usable content of
EtaleStackBaseChangePresentation at the identity point (a formula for
liftToX/liftToY plus the inverse 2-cell, or an added one-cell uniqueness field
for the two-pullback), and derive S1743SourceRetraction.  With (a) in hand, the
remaining content of (b) is the hom-level transport of S1743YonedaClassEquiv
across the model comparison plus essential surjectivity of the object map, i.e.
that every affine finite-etale scheme over Spec R' extends to a cover
(the converse direction of S1743Object).
