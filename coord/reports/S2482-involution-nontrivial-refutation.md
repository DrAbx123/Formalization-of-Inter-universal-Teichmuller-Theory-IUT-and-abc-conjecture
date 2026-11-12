# S2482 elliptic involution nontriviality and original-uniqueness refutation

## Actual (EXIT=0)
S2482QiNontrivialActual.lean:
- S2482I, S2482I_sq: a chosen square root of -1 in F.
- S2482Eval: actual F-algebra evaluation R -> F at (x,y) = (I, 1-I).
- S2482Eval_X1.
- S2482_X1_ne_zero: the class of y in R is nonzero.
- S2482CoordinateRingInvolution_ne_id: the coordinate-ring involution is not the identity.
- S2482AffineInvolution_ne_id: the scheme involution is not the identity.
- S2482EllipticInvolution_ne_id: the orbicurve involution is not Hom.id.
- S2482_original_uniqueness_field_refuted:
    assuming the source uniqueness field for S2482EllipticInvolution, False.
  Thus the current SourceSignQuotientData.unique_elliptic_involution field is inconsistent with
  the actual nontrivial [-1] involution.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Corrected uniqueness statement
Defined in S2482InvolutionUniquenessAuditActual:
  S2482CorrectedEllipticUniqueness elliptic : Prop := forall inv,
    TwoIso (comp inv inv) id -> inv != Hom.id -> inv = elliptic.
The source structure should add `ellipticInvolution_nontrivial` (or exclude Hom.id from the
quantifier) while keeping the production target semantics unchanged.

## Remaining geometry
OrbicurveSignAction: inversion and inversionSquared actual; diagram/atBase/generator_identification
still missing. cF quotient/witness, cK/scalar extensions, group data, V/V_mod_bad/epsilon still missing.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482QiNontrivialActual.lean
EXIT=0; SHA256 8499EAFDD8CA7821A0CE62300DEF674C871DBC7810252F6930BACDF947860AC7
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482QiNontrivialActual.olean
olean SHA256: 418890F61AA16A6FF929F09B18788093021EC6184B5D9F381D4DD14BE82A67B2
axioms: trio