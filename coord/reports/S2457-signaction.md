# S2457: OrbicurveSignAction/cF — exact field missing; affine square attempt incomplete

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL available:
- S2482EllipticInvolution : S2482Orbicurve.Hom S2482Orbicurve (S2482QiInvolutionActual, olean 101296).
- S2482CoordinateRingInvolution_sq : S2482CoordinateRingInvolution.comp S2482CoordinateRingInvolution = AlgHom.id F S2482CoordinateRing (S2482QiInvolutionSquareActual, EXIT=0, olean 96032).
- S2456EllipticInvolution re-export actual (olean 19008, SHA 006d372f...).

OrbicurveSignAction NOT constructed. Required fields from Iut/Foundations/Orbicurve.lean:
  diagram : SignActionIndex ->p EtaleStackPseudofunctor F
  atBase : Bicategory.Equivalence (diagram.obj signActionObject) X.stack.fiber
  inversion : X.Hom X
  generator_identification : (atBase.inv >> diagram.map signActionGenerator) >> atBase.hom ~ inversion
  inversionSquared : TwoIso (inversion >> inversion) (id X)
Only inversion is available (S2482EllipticInvolution). The pseudofunctor diagram, its atBase equivalence, and generator_identification are not constructed anywhere; no OrbicurveSignAction instance exists in the project.

Affine square attempt S2457AffineInvolutionSquareActual: prove S2482AffineInvolution >> S2482AffineInvolution = id. The Spec.map/Spec.map_eq_id reduction reaches the ring-hom equality, but the final ext step is incomplete; no olean. This is not claimed. Even if it closes, it gives only affine square, not the orbicurve TwoIso.

cF / quotient NOT constructed:
- cF : HyperbolicOrbicurve F
- quotient : OrbicurveSignInvariantMorphism signAction cF
- quotientWitness : OrbicurveSignQuotientWitness signAction quotient
No orbicurve sign quotient construction in Mathlib/project. cK also missing (scalar extension).

No fake, no IsStack claim.