# Corrected Hom uniqueness: ACTUAL

## BUILT (EXIT=0)
S2482CorrectedHomUniquenessActual.lean:
- S2482PhiRingEquiv, S2482PhiAlgEquiv, S2482Phi_classification.
- S2482CorrectedHomUniqueness:
    eta : Hom,
    Nonempty (Iso (eta.comp eta) (Hom.id X)) ->
    (not Nonempty (Iso eta (Hom.id X))) ->
    Nonempty (Iso eta S2482EllipticInvolution).
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Proof
Classification of phi gives id or sign.
- id: g=id, roundtrip S1742StrongTransIsoOfHom + S2482InducedIdIso give eta iso id, contradiction.
- sign: g=S2482AffineInvolution, S2482TwoIso_of_hom_eq gives the TwoIso.

## Next
Fill SourceSignQuotientDataCorrected.unique_elliptic_involution with this theorem; then sign action/cF/cK/epsilon and S249x integration.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482CorrectedHomUniquenessActual.lean
EXIT=0; SHA256 D394910CCB4EFE4ABA51E99784AA407A5C98D494B5DA76676F119ADC39D31B24
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482CorrectedHomUniquenessActual.olean
olean SHA256: 140EC6EA27CCB8A29990D0644D89F5603FD35DBA2F93C49A11CDD93DB6FBA896
axioms: trio