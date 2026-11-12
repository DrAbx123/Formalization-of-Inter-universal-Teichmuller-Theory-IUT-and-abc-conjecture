# S2482 orbicurves / sign action: construction status

## Actual inputs
- S2482QiCurveActual: S2482Curve: y^2=x^3-x, Delta=64, IsElliptic, S2482PuncturedCurve.
- S2482QiArithmeticActual: InitialThetaArithmeticData 5 over F=Q(i).
- S1726OrbicurveFPrimeActual: an actual geometric S1726Orbicurve over S1726K, built from the affine coordinate ring of its curve, the representable etale pseudofunctor, and realizedHyperbolicOrbicurve. This is the correct template, but its base field and curve are S1726K/E', not F/E.

## xF
The exact construction over F requires:
1. coordinate ring R = F[x,y]/(weierstrassAffinePolynomial S2482Curve);
2. the affine scheme Spec R over F (S1726AffineOver template);
3. proof schemeRepresentableEtalePseudofunctor F SpecR is a stack (S1726RepresentableIsStack template);
4. realizedHyperbolicOrbicurve F fiber isStack OrbicurveSignature.oncePuncturedElliptic ... .
Steps 1-4 are not instantiated for S2482Curve. The imported generic stack-sheaf/descent API names used by S1726 are not resolving in the current import scope; no working Lean term was produced.
Attempted file S2482QiOrbicurveActual was removed (it contained no kernel-clean declaration); do not consume it.

## cF / cK / sign action / quotient witness
Even with xF, SourceSignQuotientData requires:
- ellipticInvolution : xF.Hom xF with square = id;
- unique_elliptic_involution;
- signAction : OrbicurveSignAction xF (bicategorical pseudofunctor, equivalence at base, generator identification, inversionSquared);
- cF, quotient : OrbicurveSignInvariantMorphism signAction cF, quotientWitness : OrbicurveSignQuotientWitness;
- xK/cK over A.K, scalar extensions xKExtension/cKExtension, type equations;
- xFGroups/cFGroups, fGroupInclusion; V/V_mod_bad/epsilon.
None is constructed. S1726 only builds the geometric orbicurve, not the sign quotient package; the source card in SourceEtaleStackInstanceSupplyReduction explicitly lists these as remaining.

## Degenerate point-stack warning
The one-point constant stack (sourceStackPointEtaleFiber) inhabits Nonempty (HyperbolicOrbicurve F) only by inserting a signature via realizedHyperbolicOrbicurve. The source card says this witness has no geometric content and must not stand for the Definition 3.1 orbicurve. It was NOT used as xF.

## Exact first missing
- Actual xF: affine coordinate-ring/stack model of y^2=x^3-x over F and its realized hyperbolic orbicurve.
- elliptic involution and sign action on xF.
- quotient cF with its sign-invariant morphism and quotient witness.
- K-side base change xK/cK and scalar extensions.
- group data/inclusion, V/V_mod_bad/epsilon.
No fake/interface inhabitant was added; no new compile is claimed.