# S2482 involution square and TwoIso: actual

## BUILT (EXIT=0)
- S2482CoordinateRingInvolution_sq: algebra involution squared = id.
- S2482AffineInvolution_sq: scheme endomorphism squared = identity in Over F.
  Proof: Over.OverMorphism.ext; Spec.map_comp; CommRingCat.ofHom_comp; ring-hom square; Spec.map_id.
- S2482InducedIdIso: actual 2-isomorphism StrongTrans.id ≅ S1742StrongTransOfHom (𝟙 xF).
- S2482EllipticInvolution_comp_underlying: underlying scheme map of the vcomp square is 𝟙.
- S2482EllipticInvolution_square:
    HyperbolicOrbicurve.Hom.TwoIso
      (Hom.comp S2482EllipticInvolution S2482EllipticInvolution)
      (Hom.id S2482Orbicurve).
  Proof: scheme square + S2398HomOfStrongTrans_vcomp + S1742StrongTransIsoOfHom + S2482InducedIdIso, inverted.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Still missing
- uniqueness of the elliptic involution (2-cell Subsingleton argument).
- OrbicurveSignAction (generator identification, inversionSquared).
- cF quotient/witness, cK/scalar extensions, group data, V/V_mod_bad/epsilon.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482QiInvolutionSquareActual.lean
EXIT=0; SHA256 9D871E2317E24ADA3B7ACD5B8394E773D3437F9A6736A42C7E3B62E6DB06DF72
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482QiInvolutionSquareActual.olean
olean SHA256: 4EDEF9B0B8B5A0B3FCE3A23B94E6EDD9FE9F0BDEEB774750A4A638EC49806A96