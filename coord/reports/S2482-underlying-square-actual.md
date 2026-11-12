# Underlying compression and square bridge: actual

## BUILT (EXIT=0)
S2482UnderlyingSquareActual.lean:
- S1742HomOfStrongTrans_vcomp (raw StrongTrans level):
    underlying (vcomp eta theta) = underlying eta ≫ underlying theta.
- S2482HomOfStrongTrans_comp (Hom-specific via S2482Underlying abbrev).
- S2482HomOfStrongTrans_square_of_iso:
    Nonempty (Iso (η.comp η) (Hom.id X)) ->
    S2482Underlying η ≫ S2482Underlying η = 1.
Axioms: propext, Classical.choice, Quot.sound; no sorryAx.

## Remaining
Spec.map_surjective -> phi algebra automorphism; phi^2=id; classification -> phi=id or sign;
sign -> S2482TwoIso_of_hom_eq; corrected Hom field with 2-iso-class nontriviality; sign action/cF/cK/epsilon.
No fake.

## Artifacts
Lean: tmp/sheaf/xif/paper/S2482UnderlyingSquareActual.lean
EXIT=0; SHA256 3E64809351EAED36B1A105B39D5E39C9A472875DA1F3B39FF840B7BBBC5DE031
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2482UnderlyingSquareActual.olean
olean SHA256: 6237276E6BCBD9479A9B180D6A9D070C9A90C5BA1F1C02BE888E003E27F0FD63
axioms: trio