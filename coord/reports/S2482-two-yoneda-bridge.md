# 2-Yoneda bridge: actual

## BUILT (EXIT=0)
S2482TwoYonedaBridgeActual.lean:
- S2482HomOfStrongTrans_ellipticInvolution:
    S1742HomOfStrongTrans S2482EllipticInvolution = S2482AffineInvolution.
- S2482TwoIso_of_hom_eq:
    for eta : S2482Orbicurve.Hom S2482Orbicurve,
    S1742HomOfStrongTrans eta = S2482AffineInvolution ->
    Nonempty (Iso eta S2482EllipticInvolution).
Proof: S1742StrongTransIsoOfHom eta : induced(underlying eta) ≅ eta; rewrite underlying eta
to S2482AffineInvolution and use the definition of S2482EllipticInvolution.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Exact remaining for corrected Hom uniqueness
1. From square=id TwoIso for eta, derive underlying g^2=id (via roundtrip iso + S2398HomOfStrongTrans_vcomp
   + S1742HomOfStrongTrans_congr).
2. Extract algebra automorphism phi from g using Spec.map_surjective; prove phi^2=id.
3. Apply S2482OrderTwoAlgAutClassification_actual; get phi=id or sign.
4. If phi=sign, S2482TwoIso_of_hom_eq gives the required TwoIso.
5. Subtlety: `eta != Hom.id` does not by itself imply underlying eta != id, because strong
   transformations may differ by 2-isomorphism. Need either prove Hom is determined by underlying
   map (StrongTrans equality/discreteness) or change the corrected hypothesis to nonidentity of
   the underlying scheme map/2-isomorphism class.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482TwoYonedaBridgeActual.lean
EXIT=0; SHA256 0661501A88BE883BFE9728D4B8545917BC0BBC6292FEA91C9006861218EA4956
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482TwoYonedaBridgeActual.olean
olean SHA256: B99893DC4DE900E2999F9D9788BAD422D6BB932DFF533D805910BF8B22A3863F
axioms: trio