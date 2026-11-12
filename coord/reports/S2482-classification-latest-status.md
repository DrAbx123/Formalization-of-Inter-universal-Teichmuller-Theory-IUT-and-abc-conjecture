# S2482 order-two classification: latest status

## Actual baseline
- S2482QiNontrivialActual.lean: nontriviality + original uniqueness refutation actual; SHA 380587FF..., olean 645F6D3A....
- S2482CorrectedSourceSignQuotientActual.lean: corrected TwoIso interface; SHA 53E074A7..., olean 828901E3....
- S2482InvolutionUniquenessAuditActual.lean: corrected TwoIso Prop; SHA D339C8C2..., olean FB83D0AF....

## Classification still missing
S2482OrderTwoAlgAutClassification has no inhabitant.
The branch-point route requires function-field/Mobius classification; Mathlib has no formalized
branch-point permutation argument for this curve.

## Useful Mathlib API found
Mathlib's Weierstrass affine coordinate ring has:
- CoordinateRing.basis : Basis (Fin 2) F[X] W.CoordinateRing;
- CoordinateRing.norm_smul_basis;
- CoordinateRing.degree_norm_smul_basis [IsDomain F] :
    degree (norm (p • 1 + q • Y)) = max (2*degree p) (2*degree q + 3);
- CoordinateRing.natDegree_norm_ne_one.
These can support a norm-degree classification once our R is identified with W.CoordinateRing.
The identification R ~= W.CoordinateRing and the deduction that an automorphism preserves the
norm-degree filtration are not assembled.

## New caution on branch-point route
An order-two Mobius map preserving {0,1,-1,infinity} need not be only x or -x: e.g. x -> 1/x,
x -> -1/x, and others also preserve the set. Additional ramification/genus data (or the norm-degree
argument above) is needed to exclude them. The previous branch-point plan as stated is therefore
incomplete; no fake shortcut is taken.

## Remaining geometry
signAction diagram/atBase/generator_identification, cF quotient/witness, xF/cF groups,
xK/cK/scalar extensions, epsilon remain missing. Place fields actual via S2490PlaceFieldsA.

## Artifacts
No new actual file compiled for this classification attempt; existing actual files remain as above.