# Corrected SourceSignQuotientData inhabitant: actual components and exact missing

## Actual components available for A = S2482Arithmetic.arithmeticData (l=5)
- xF = S2482Orbicurve (S2482QiOrbicurveActual, EXIT=0).
- xF_geometry = S2482OncePuncturedGeometry (S2482QiOrbicurveActual).
- ellipticInvolution = S2482EllipticInvolution (S2482QiInvolutionActual).
- ellipticInvolution_squared = S2482EllipticInvolution_square (S2482QiInvolutionSquareActual).
- ellipticInvolution_nontrivial = S2482EllipticInvolution_ne_id (S2482QiNontrivialActual).
- corrected uniqueness statement: S2482CorrectedEllipticUniqueness (S2482InvolutionUniquenessAuditActual), not inhabited.
- place block: S2490PlaceFieldsA : S2490AllPlacesFields S2490A, and S2490A is definitionally S2482Arithmetic.arithmeticData; provides V, V_mod_bad, oddness, nonempty, V_section, V_eq_section, V_mod_bijection, V_place_comap.
  Source: tmp/sheaf/xif/paper/S2490RestrictionSectionActual.lean (EXIT=0 actual).

## Exact missing fields (in SourceSignQuotientDataCorrected order)
1. signAction : Iut.OrbicurveSignAction S2482Orbicurve.
   Only inversion and inversionSquared are actual. Missing diagram : SignActionIndex ⥤ᵖ EtaleStackPseudofunctor F, atBase equivalence, generator_identification.
2. signAction_inversion_eq_ellipticInvolution: follows once signAction is built with inversion := S2482EllipticInvolution.
3. unique_elliptic_involution corrected: forall inv, square=id -> inv != Hom.id -> inv = S2482EllipticInvolution.
   Missing classification of order-two automorphisms of the curve/stack; no proof in tree.
4. cF : Iut.HyperbolicOrbicurve A.F. Missing actual sign quotient stack.
5. quotient : OrbicurveSignInvariantMorphism signAction cF. Missing.
6. quotientWitness : OrbicurveSignQuotientWitness signAction quotient. Missing.
7. xFGroups/cFGroups : SourceOrbicurveGroupData ... Missing actual etale fundamental group data.
8. fGroupInclusion : ProfiniteFundamentalGroupInclusion ... Missing.
9. xK/cK : Iut.HyperbolicOrbicurve A.K. Missing actual K-side orbicurves.
10. xKExtension/cKExtension : SourceOrbicurveScalarExtension A.F A.K xF/cF. Missing.
11. xKType/cKType: signatures (1,l-tors) and (1,l-tors)^+-. Missing with xK/cK.
12. xK_eq_extension/cK_eq_extension. Missing.
13. epsilon : OrbicurveBoundaryCusp cK. Depends on cK; missing.

## Conclusion
The corrected interface is actual and the F-side involution package plus the eight place fields are actual.
A full inhabitant is blocked exactly at signAction (diagram/atBase/generator_identification), cF quotient/witness,
xF/cF group data, xK/cK scalar extensions, and epsilon. No fake inhabitant was introduced; production target unchanged.

## Artifacts
- S2482CorrectedSourceSignQuotientActual.lean (corrected interface, EXIT=0; SHA 2E3C1B9D..., olean 5022BB6A...).
- S2482QiNontrivialActual.lean (nontriviality/refutation, EXIT=0; SHA 8499EAFD..., olean 418890F6...).