# S2458: OrbicurveSignAction diagram/atBase — exact type blocker

Date: 2026-11-02. Serialized lake env lean -j1.

Goal: diagram : SignActionIndex ->p EtaleStackPseudofunctor F, obj signActionObject = S2482Orbicurve.stack.fiber, map signActionGenerator = S2482EllipticInvolution.

BLOCKER (type-level): a pseudofunctor must provide mapComp for composable pairs. For f=g=g=signActionGenerator, SignGroup=Multiplicative (ZMod 2) has g >> g = id signActionObject, so mapComp g g must be an isomorphism
  map (id signActionObject) ~ (S2482EllipticInvolution >> S2482EllipticInvolution)
i.e. exactly
  TwoIso (S2482EllipticInvolution >> S2482EllipticInvolution) (id S2482Orbicurve).
This is OrbicurveSignAction.inversionSquared. It is NOT available at orbicurve level; only S2482CoordinateRingInvolution_sq (coordinate ring) and an incomplete affine square attempt exist.

Consequences:
- diagram cannot be written even as a partial object: mapComp(g,g) is a required field, not an optional one.
- atBase : Bicategory.Equivalence (diagram.obj signActionObject) X.stack.fiber cannot be typed until diagram exists; Bicategory.Equivalence.id is actual but its type depends on diagram.obj.
- generator_identification is also after diagram.
- cF/quotient/witness remain blocked.

ACTUAL retained: S2456EllipticInvolution re-export (oleans 19008, SHA 006d372f...), S2482QiInvolution actual (101296), S2482CoordinateRingInvolution_sq (96032).

No actual diagram/atBase/cF is claimed; no fake, no IsStack.