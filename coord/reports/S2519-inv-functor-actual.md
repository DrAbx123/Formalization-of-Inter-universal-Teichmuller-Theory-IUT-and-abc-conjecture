# S2519 inverse functor: ACTUAL

## BUILT (EXIT=0)
S2519InvFunctorActual.lean:
- S2519InvFunctor : FiniteEtaleCover S2482AffineScheme ⥤ OrbicurveFiniteEtaleCover S2482Orbicurve.
  obj = S2517InvObj; map = Quot.mk of S2518InvCoverMap; laws checked with
  backward.isDefEq.respectTransparency false.
Axioms trio; no sorryAx.

## Next
- Faithful: 2-iso of images -> base cover map equality.
- Full: any cover map is 2-iso to S2518InvCoverMap of a base map.
- EssSurj: base-change at identity point recovers any cover.
No fake.

## Artifacts
EXIT=0; SHA256 36C364FE4705CCD227F89C19388831E55007BF38D5C2D43A74EC26CEDE1FC99D
olean SHA256: 36259E4763CD8A1D7A4CAC3BD40E1DB329FE04B02C09B4BE000EF0FE1DA93E9B
axioms: trio