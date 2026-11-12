# S2482 elliptic involution: actual endomorphism of xF

Layer: O (IUT I Definition 3.1(b), elliptic involution).

## BUILT (EXIT=0)
- S2482AffineInvolutionAlgHom: MvPolynomial (Fin 2) F -> MvPolynomial (Fin 2) F, x0 maps to x0, x1 maps to -x1.
- S2482AffineInvolutionAlgHom_polynomial: it fixes weierstrassAffinePolynomial S2482Curve.
- S2482CoordinateRingInvolution: induced F-algebra endomorphism of R=F[x,y]/(y^2-x^3+x).
- S2482AffineInvolution: scheme endomorphism of Spec R over F.
- S2482EllipticInvolution: endomorphism of S2482Orbicurve via S1742StrongTransOfHom.

## Axioms
#print axioms (probe): propext, Classical.choice, Quot.sound only; no sorryAx.

## Still missing
- square=id TwoIso for S2482EllipticInvolution.
- uniqueness of the elliptic involution.
- OrbicurveSignAction with generator identification/inversionSquared.
- cF quotient and witness.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482QiInvolutionActual.lean
EXIT=0; SHA256 311AB7E35DA11A1C976A80D5FE979DE6210B9D2B00C722842B688A917A237421
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482QiInvolutionActual.olean
olean SHA256: 015F600C73635A47F23F508E4A30B5BA2F4A65F7DC2732A6A4860661871640A0