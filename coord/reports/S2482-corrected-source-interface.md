# Corrected SourceSignQuotientData interface: actual definition

## Actual (EXIT=0)
S2482CorrectedSourceSignQuotientActual.lean defines
  SourceSignQuotientDataCorrected (A : InitialThetaArithmeticData l) : Type (u+1)
with the full source field list except the inconsistent uniqueness field, and with:
- ellipticInvolution_nontrivial : ellipticInvolution != Hom.id xF;
- unique_elliptic_involution : forall inv, square=id -> inv != Hom.id -> inv = ellipticInvolution.
This is the corrected interface qside/primespine may reference. It does not modify the production target.

## Dependency
The file imports SourceDefinition31Quantifiers and S2482QiNontrivialActual; no sorry/axiom.

## Inhabitant status
No inhabitant is constructed. Exact missing fields to inhabit it:
- xF: S2482Orbicurve + S2482OncePuncturedGeometry actual.
- ellipticInvolution: S2482EllipticInvolution actual; squared: S2482EllipticInvolution_square actual;
  nontrivial: S2482EllipticInvolution_ne_id actual.
- unique_elliptic_involution corrected: not proved (needs classification of involutions/automorphisms).
- signAction: OrbicurveSignAction S2482Orbicurve; only inversion and inversionSquared actual,
  diagram/atBase/generator_identification missing.
- cF + quotient + quotientWitness: missing.
- xFGroups/cFGroups/fGroupInclusion: missing.
- xK/cK, scalar extensions, type equations: missing.
- V/V_mod_bad/V_section/V_mod_bijection/V_place_comap: missing.
- epsilon: missing.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482CorrectedSourceSignQuotientActual.lean
EXIT=0; SHA256 2E3C1B9D2F9BFC2E57E77C6B1C68A5E711985AE4FFEAD22C6A5260C5F310F0F8
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482CorrectedSourceSignQuotientActual.olean
olean SHA256: 5022BB6AF83BEF1F955C8107B9962EF18450736FEC5D4DFE112278C62FE38F05
Axioms: structure/type definition, no theorem closure; no sorryAx.