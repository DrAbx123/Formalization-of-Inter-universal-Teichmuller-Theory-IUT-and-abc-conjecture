# Corrected uniqueness: classification and equality-vs-2-iso issue

## Actual (EXIT=0)
S2482QiNontrivialActual.lean now proves:
- S2482_X1_ne_zero.
- S2482CoordinateRingInvolution_ne_id.
- S2482AffineInvolution_ne_id.
- S2482EllipticInvolution_ne_id.
- S2482_original_uniqueness_field_refuted.
- S2482OrderTwoAlgAutClassification (Prop, no inhabitant).
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Exact missing classification
S2482OrderTwoAlgAutClassification:
  forall phi : R ~= R, phi^2=id -> phi=id or phi=S2482CoordinateRingInvolution.
Proof plan remains: affine equivalence/Spec fully faithful -> algebra automorphism; phi fixes x
(hyperelliptic quotient), phi(y)=±y; nonidentity excludes +y. This classification is not formalized.

## Important correction on the target form
Even after the algebra classification, the corrected field as **equality of Hom**
  forall inv, square=id -> inv != id -> inv = S2482EllipticInvolution
does not follow from a 2-Yoneda comparison: Spec/2-Yoneda gives a 2-isomorphism between strong
transformations, not equality. S1932StrongTransSubsingleton shows 2-cells are subsingleton, but
this does not identify distinct strong transformations. The corrected field should therefore be
  forall inv, square=id -> inv != id -> Nonempty (TwoIso inv S2482EllipticInvolution)
or equivalently a 2-isomorphism (with inversion convention). The equality form is too strong unless
a separate strong-trans equality theorem is proved.

## Remaining geometry
OrbicurveSignAction diagram/atBase/generator_identification, cF quotient/witness, xF/cF group data,
xK/cK/scalar extensions, epsilon: missing. Place data actual via S2490PlaceFieldsA.

## Artifacts
S2482QiNontrivialActual.lean EXIT=0; SHA256 380587FFE4B9A3A0338079C4AC2DD439BDE9F46BDC8EB3B200A763FC1971C070; olean SHA256 645F6D3A16A6E1C2A6B5B0D88EC339D018D141330C78931E95DF37A18C4C2C0D.