# S1674: actual representable StrongTrans stack lift

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve over S1280 F; representing affine scheme S1419AffineOver = Spec R, R=K[x,y]/(y^2+xy-x^3-5).
Domain: actual S1348 affine coordinate ring/scheme and schemeRepresentableEtalePseudofunctor; no cover category/group product/l-torsion.
Direction: actual construction of the StrongTrans stack lift; square/nonidentity/signAction/quotient still missing.

BUILT:
- S1674App: app component of the representable StrongTrans by postcomposition with a scheme endomorphism.
- S1674StrongTransOfSchemeEndo: actual Pseudofunctor.StrongTrans S1674F S1674F.
- S1674StackLift : S1536XF.Hom S1536XF, instantiated at S1670SchemeEndo.
- S1674IdentityHom : S1536XF.Hom S1536XF.
- exact missing types S1674StackLiftNonidentityRequired, S1674SquareTwoIsoRequired, S1674SignActionRequired, S1674SignQuotientRequired.

PROVED:
- The representable StrongTrans app/naturality/coherence fields are actual (discrete-category subsingleton proofs).
- S1674SchemeEndo from S1670 is actual and feeds S1674StackLift.

MISSING:
- S1674StackLift != identity (nonidentity).
- TwoIso (comp stackLift stackLift) identity (square).
- OrbicurveSignAction and OrbicurveSignQuotientWitness/quotient.
No fake signAction/quotient; no group product/l-torsion/terminal.

Consumer: S1536 SourceSignQuotientGeometricCore/Data (xF, ellipticInvolution, signAction, quotient) -> A/F source-object chain.

Reports read: MAINLINE_ABC_F.md; gap-exploration-20261030.md §备选路线; S1449-report-ABC-graph.md §0; 心得.md; ACTUAL-OBLIGATIONS-CLASSIFICATION.md.

Lean: tmp/sheaf/xif/paper/S1674StackStrongTransActual.lean
EXIT=0; SHA256 53CC3853A237625D002E3D6FFB5CCBA56E15FD55AE018DE1A43DE3886C2A8676
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1674StackStrongTransActual.olean