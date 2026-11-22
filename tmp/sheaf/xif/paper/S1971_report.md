# S1971: pointwise sign-action 2-colimit and the exact first missing

File: tmp/sheaf/xif/paper/S1971ActionStackificationActual.lean
Namespace: LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual

## Build evidence

- EXIT = 0 (lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1971ActionStackificationActual.olean ...)
- Source: 15612 bytes, SHA256 39C4A145E9C9EE47E479770C3ED35E80D5C1A1BA8A7DA8D3A786B987F94B4F5C
- Olean: 300744 bytes, SHA256 84A78E1AFDF594E72906DC3F8A8F14CEF853C7618771C73734FBDE1FBE9FCDCF
- #print axioms on every audited declaration: propext, Classical.choice, Quot.sound only.
- Consumer _S1971Consumer.lean: EXIT = 0.
- No sorry, no admit, no sorryAx, no new axiom, no fake IsStack instance.

## What is constructed (step 1, and the single-morphism part of step 2)

- S1971SchemeAut: the actual sign-group action on the S1726 affine model by the
  actual elliptic involution S1898AffineEndo; its multiplication law is
  S1971SchemeAut_mul, using S1932AffineEndo_comp ([-1]^2 = 1) and
  S1963SignGroup_mul_eq_one.
- S1971PointMulAction: the induced MulAction on the type of U-points.
- S1971PointwiseQuotient U: the pointwise action category (Grothendieck
  construction) of the sign action at U.
- S1971PointwiseQuotient_hom: (P -> Q) is exactly the subtype of sign elements
  g with g . P = Q; this is the action-groupoid morphism type, not an orbit set.
- S1971PointwiseQuotient_fixed_nontrivial_aut: a point fixed by the nontrivial
  sign element has a nonidentity automorphism in the pointwise colimit; the
  construction is genuinely stacky at fixed points.
- S1971ActionMap: a generic equivariant-map functor between action categories.
- S1971PrecompFunctor: restriction of the pointwise colimit along every
  morphism of test schemes, with object/map computation lemmas.

## The exact first missing

- S1971FunctorialPointwiseColimit: the global category-valued pseudofunctor on
  the etale site whose fiber at every U is S1971PointwiseQuotient U.  This is
  the coherence assembly of the S1971PrecompFunctor family; the object and
  morphism maps are formalized, the strict functor coherence equations are not.
- S1971Stackification Q: Pseudofunctor.IsStack for Q.  The pointwise action
  category sees only the trivial sign-torsor; an etale stack must see all
  sign-torsors.  Mathlib has no Cat-valued stackification.
- S1971QuotientStack: the conjunction of the two missing data.
- S1971StackQuotientWitness: the full S1964 package (stack fiber with the
  pointwise colimits, sign-invariant quotient, bicategorical universal property).
  S1964FirstMissing_ofStackQuotientWitness shows that this witness yields
  S1964QuotientStructure; no converse is asserted.

## Why this is not a fake quotient

The pointwise category is the honest action groupoid of the actual involution.
It has the correct fixed-point stabilizers (S1971PointwiseQuotient_fixed_nontrivial_aut),
so it is not the coarse orbit set.  It is not claimed to be a stack, and no
quotient structure or IsStack instance is postulated.  The global pseudofunctor,
its stack condition and the universal property are left as explicit Prop-valued
missing targets.

## Next executable step

Prove the two coherence equalities for S1971QuotientPrestackFunctor: map_id and
map_comp for the strict functor U |-> S1971PointwiseQuotient U, using
S1971PrecompFunctor_obj_back and S1971PrecompFunctor_map_val.  The remaining
map equality is the eqToHom-adjusted equality of action-category morphisms;
the obstruction is the strict coherence of precomposition with identity and
composition in the action category, not the mathematics of the involution.