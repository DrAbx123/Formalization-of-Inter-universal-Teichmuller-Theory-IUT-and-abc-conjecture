# Classification actual and corrected algebra uniqueness

## Classification ACTUAL (independently recompiled)
S2482OrderTwoAlgAutClassificationAltActual.lean:
  S2482OrderTwoAlgAutClassification_actual : S2482OrderTwoAlgAutClassification.
Target imported from S2482QiNontrivialActual; axioms propext/Classical.choice/Quot.sound.
Source SHA256 406B9E872B7418AABE462C72E4E08C62A562EB4D54D42ECAB93D5D99504E628A
OLean SHA256 D6492DF199BB5EC6536B14D292FE046F1DCEC79EF8983B754F3E1985DC8D6B5C.

## Corrected algebra uniqueness ACTUAL
S2482CorrectedUniquenessAlgActual.lean:
  S2482_corrected_uniqueness_alg (phi : R ~= R)
    (phi^2=id) (phi != id) : phi.toAlgHom = S2482CoordinateRingInvolution.
Follows immediately from the classification target.
Source SHA256 8B225D177D7CFBEB091CA20C1B8C9B2B698112D3059B0857767DA35B21302D8A
OLean SHA256 7021973C37FFB6CC5314B5EBE7C315B7AA9F2ECD6D24F4A017EBF2820D2CEA5E.
Axioms trio; no sorryAx.

## Still missing
- Corrected uniqueness in the Hom/TwoIso form for arbitrary strong transformations:
  need Spec.map_surjective to extract the algebra automorphism from the underlying scheme map,
  show square=id and nonidentity transfer, then use S1742StrongTransIsoOfHom to get
  Nonempty (TwoIso inv S2482EllipticInvolution).
- OrbicurveSignAction diagram/atBase/generator_identification.
- cF quotient/witness, xK/cK scalar extensions, epsilon; S2492/S2495/S2497/S2498 integration not done.

## Artifacts
- tmp/sheaf/xif/paper/S2482OrderTwoAlgAutClassificationAltActual.lean
- tmp/sheaf/xif/paper/S2482CorrectedUniquenessAlgActual.lean
Both EXIT=0; queue appended.