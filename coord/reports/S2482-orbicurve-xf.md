# S2482 xF actual: affine orbicurve over F=Q(i)

Layer: O (IUT I Definition 3.1(b) xF over F=Q(i)).

## BUILT (EXIT=0)
- S2482AffinePolynomial = weierstrassAffinePolynomial S2482Curve (y^2=x^3-x).
- S2482CoordinateRing = F[x,y]/(weierstrassAffinePolynomial).
- S2482AffineScheme = Spec R, S2482AffineOver : SchemeOverField F.
- S2482RepresentableIsStack: representable etale pseudofunctor is an etale stack (S1419/N8Closure discrete-sheaf-stack construction).
- S2482Orbicurve : Iut.HyperbolicOrbicurve F via realizedHyperbolicOrbicurve with once-punctured elliptic signature.
- S2482OncePuncturedGeometry : SourceOncePuncturedGeometry S2482PuncturedCurve S2482Orbicurve.

## Exact missing (sign quotient package)
- ellipticInvolution : S2482Orbicurve.Hom S2482Orbicurve with square=id and uniqueness.
- OrbicurveSignAction S2482Orbicurve.
- cF with SignInvariantMorphism and SignQuotientWitness.
- K-side xK/cK, scalar extensions, group data, V/V_mod_bad/epsilon.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482QiOrbicurveActual.lean
EXIT=0; SHA256 DA6D1168B060591AFF551002C695CAA6D01ED3D126BB539FAC2BD55E5176219A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482QiOrbicurveActual.olean
olean SHA256: 6D613C9049D4052A16E0787B822D47CFCD858B1BE9A5888152812BDA34DA22DD
axioms: propext, Classical.choice, Quot.sound; no sorryAx.

No fake/degenerate point stack used; the affine model of the actual curve is the geometric input.