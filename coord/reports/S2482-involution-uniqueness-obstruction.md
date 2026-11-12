# S2482 involution uniqueness audit: identity obstruction and correction

## Actual (EXIT=0)
- S2482IdentityTwoIso: identity always satisfies the square=id hypothesis.
- S2482_unique_elliptic_involution_forces_identity: the source uniqueness field forces ellipticInvolution = Hom.id.
- S2482CorrectedEllipticUniqueness (definition, not inhabited):
    forall inv, TwoIso (comp inv inv) id -> inv != Hom.id -> inv = elliptic.
- S2482EllipticInvolutionNontrivial (definition): S2482EllipticInvolution != Hom.id.
Axioms for the constructed theorem: propext, Classical.choice, Quot.sound; no sorryAx.

## Source correction required
The uniqueness field must add `inv != Hom.id xF` (or an equivalent nontriviality predicate).
Without it, identity alone satisfies the hypothesis and forces ellipticInvolution = id, contradicting
the intended [-1] involution. No production structure was modified.

## Exact remaining goal for formal refutation
S2482EllipticInvolutionNontrivial, equivalently S2482AffineInvolution != 1, equivalently
S2482CoordinateRingInvolution != AlgHom.id.
Reduces to `[y] != 0` and `2 != 0` in R=F[x,y]/(y^2-x^3+x). This was not completed;
the attempted nontriviality file was removed (not consumed).

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482InvolutionUniquenessAuditActual.lean
EXIT=0; SHA256 C2F6456565C5B1CA84DCA11A5044D199EF2F13C5CCDFA6FDEDD067D8049275F2
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482InvolutionUniquenessAuditActual.olean
olean SHA256: D1E3417850D5E6D0C2B5883F2BA75E78560138038A681D0D9340161EE4580187
axioms: propext, Classical.choice, Quot.sound