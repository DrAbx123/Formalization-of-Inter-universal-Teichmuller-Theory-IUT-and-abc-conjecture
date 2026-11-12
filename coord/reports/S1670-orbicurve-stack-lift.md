# S1670: scheme endomorphism of S1419AffineOver; exact missing StrongTrans

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve over S1280 F; representing affine scheme S1419AffineOver = Spec R, R=K[x,y]/(y^2+xy-x^3-5).
Domain: actual S1348 affine coordinate ring and scheme; no cover category, no group product, no l-torsion.
Direction: actual construction (scheme level proven; stack StrongTrans missing).

BUILT:
- S1670SchemeEndo : S1419AffineOver l -> S1419AffineOver l, induced by S1653CoordEndo (x|->x, y|->-x-y).
- S1670IdentityHom : S1536XF.Hom S1536XF.
- exact missing types S1670MissingStrongTrans, S1670MissingNontrivialLift, S1670SquareTwoIsoRequired, S1670SignActionRequired, S1670SignQuotientRequired.

PROVED:
- S1670CoordEndo_comp_algebraMap: the coordinate endomorphism is over F.
- S1670SchemeEndo is a well-defined morphism in Over (Spec F).
- Identity Hom is actual.

MISSING:
- Actual nontrivial Pseudofunctor.StrongTrans / HyperbolicOrbicurve.Hom stack lift of S1670SchemeEndo to S1536XF.Hom S1536XF.
- Square TwoIso = id and nonidentity proof.
- OrbicurveSignAction and OrbicurveSignQuotientWitness.
No fake StrongTrans/signAction/quotient; missing types only.

Consumer: S1536 SourceSignQuotientGeometricCore/Data (xF, ellipticInvolution, signAction, quotient) -> A/F source-object chain.

Reports read:
- D:/lean/coord/MAINLINE_ABC_F.md
- D:/lean/coord/reports/gap-exploration-20261030.md (备选路线)
- D:/lean/coord/reports/S1449-report-ABC-graph.md §0
- D:/lean/心得.md
- D:/lean/coord/ACTUAL-OBLIGATIONS-CLASSIFICATION.md

Lean: tmp/sheaf/xif/paper/S1670OrbicurveStackLiftActual.lean
EXIT=0; SHA256 04E97D862FFA8D2190C54D7E83754AFCE26CC4DBD3A967FF401D13AE5A89470F
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1670OrbicurveStackLiftActual.olean

No fake Hom/signAction, no Shrink/ULift, no group product/l-torsion/terminal.