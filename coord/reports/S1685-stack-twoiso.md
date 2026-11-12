# S1685: scheme endomorphism square actual; stack TwoIso missing

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve; S1419AffineOver = Spec R, R=K[x,y]/(y^2+xy-x^3-5).
Domain: actual S1348 coordinate ring and scheme endomorphism; no cover category/group product/l-torsion.
Direction: actual scheme-level square proved; stack TwoIso/nonidentity/signAction/quotient exact missing.

BUILT/PROVED:
- S1685SchemeEndo_sq: S1670SchemeEndo composed with itself = identity on S1419AffineOver.
- S1683CoordEndo_sq and S1683PolyEndo_sq imported and used.
- S1674StackLift : S1536XF.Hom S1536XF remains actual.

MISSING:
- S1685StackLiftNonidentityRequired: S1674StackLift != S1674IdentityHom.
- S1685SquareTwoIsoRequired: TwoIso (comp S1674StackLift S1674StackLift) (id S1536XF).
- OrbicurveSignAction and OrbicurveSignQuotientWitness/quotient.
No fake TwoIso/signAction/quotient; no group product/l-torsion/terminal.

Consumer: S1536 SourceSignQuotientGeometricCore/Data -> A/F source-object chain.

Reports read: MAINLINE_ABC_F.md; gap-exploration-20261030.md §备选路线; S1449-report-ABC-graph.md §0; 心得.md; ACTUAL-OBLIGATIONS-CLASSIFICATION.md.

Lean: tmp/sheaf/xif/paper/S1685StackTwoIsoActual.lean
EXIT=0; SHA256 1DBEC3D703A78B7E5DAEE34C200F5F8D975943A16A6D4B0182C81BF255D04872
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1685StackTwoIsoActual.olean