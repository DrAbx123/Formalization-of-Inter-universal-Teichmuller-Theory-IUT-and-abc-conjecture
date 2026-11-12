# S1683: coordinate involution square; stack square/nonidentity missing

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve over S1280 F; S1419AffineOver = Spec R, R=K[x,y]/(y^2+xy-x^3-5).
Domain: actual S1348 affine coordinate ring and scheme endomorphism; no cover category/group product/l-torsion.
Direction: actual coordinate-ring involution square proved; stack TwoIso/nonidentity and signAction/quotient remain exact missing.

BUILT:
- S1683PolyEndo_sq: S1653PolyEndo.comp S1653PolyEndo = id on MvPolynomial.
- S1683CoordEndo_sq: S1653CoordEndo.comp S1653CoordEndo = id on S1348CoordinateRing.
- S1674StackLift : S1536XF.Hom S1536XF remains the actual stack lift from S1674.
- exact missing types S1683SchemeEndoSqRequired, S1683StackLiftNonidentityRequired, S1683SquareTwoIsoRequired, S1683SignActionRequired, S1683SignQuotientRequired.

PROVED:
- The coordinate endomorphism (x,y) -> (x,-x-y) is an involution on the actual coordinate ring.
- The actual stack lift S1674StackLift exists (from S1674).

MISSING:
- S1670SchemeEndo composed with itself equals identity (scheme-level square).
- S1674StackLift != identity.
- TwoIso (S1674StackLift composed with itself) identity.
- OrbicurveSignAction and OrbicurveSignQuotientWitness/quotient.
No fake signAction/quotient/StrongTrans; no group product/l-torsion/terminal.

Consumer: S1536 SourceSignQuotientGeometricCore/Data (xF, ellipticInvolution, signAction, quotient) -> A/F source-object chain.

Reports read: MAINLINE_ABC_F.md; gap-exploration-20261030.md §备选路线; S1449-report-ABC-graph.md §0; 心得.md; ACTUAL-OBLIGATIONS-CLASSIFICATION.md.

Lean: tmp/sheaf/xif/paper/S1683StackInvolutionActual.lean
EXIT=0; SHA256 2ED9770E32770A7DA395AC9A5CF80FEDB55B1C88C564A64B838504723FE49BAF
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1683StackInvolutionActual.olean