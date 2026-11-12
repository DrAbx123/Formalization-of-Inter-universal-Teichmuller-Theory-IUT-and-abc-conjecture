# S2534 cover hom map: ACTUAL

## BUILT (EXIT=0)
S2534CoverHomMapActual.lean:
- S2534AlgCoverMap (f : A ⟶ B) : finiteEtaleAlgebraCover F B ⟶ finiteEtaleAlgebraCover F A.
  Variance is reversed because covers are opposite to finite etale algebras.
  Proof uses AdjoinRoot.ringHom_ext + S2535_commutes_adjoinRoot/root.
- S2534CoverMap (f : A ⟶ B) : OrbicurveFiniteEtaleCoverMap (S2533ObjectMap B) (S2533ObjectMap A).
  Route: base-change S2534AlgCoverMap to S2482AffineScheme, then S2518InvCoverMap.
Axioms trio; no sorryAx.

## Next
Quotient to category Hom and prove injective/surjective.
No fake.

## Artifacts
EXIT=0; SHA256 98222D9FAC7D3D8D3185FF97ECAFC0C0ADEDD6FE23E825A96AAC25BB6B5538D3
olean SHA256: 018D4702888CE2A71B0EE0CAC88B0A153244BCE6E38C9B4287CA69FDB5CF5623
axioms: trio