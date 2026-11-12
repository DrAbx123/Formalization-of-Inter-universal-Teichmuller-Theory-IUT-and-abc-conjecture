# S1689: scheme square actual; StrongTrans functoriality/TwoIso missing

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve; S1419AffineOver = Spec R, R=K[x,y]/(y^2+xy-x^3-5).
Domain: actual coordinate ring/scheme endomorphism; no cover category/group product/l-torsion.
Direction: actual scheme square proved; stack functoriality/TwoIso/nonidentity exact missing.

BUILT/PROVED:
- S1689SchemeEndo_sq: S1670SchemeEndo composed with itself = identity (re-export of S1685).
- S1674StackLift actual remains available.

MISSING exact:
- S1689StrongTransFunctorialityMissing: vcomp (st e) (st e) = st (e ≫ e) for S1674StrongTransOfSchemeEndo.
- S1689StackLiftNonidentityRequired: S1674StackLift != S1674IdentityHom.
- S1689SquareTwoIsoRequired: TwoIso (comp S1674StackLift S1674StackLift) id.
- OrbicurveSignAction and OrbicurveSignQuotientWitness/quotient.
No fake TwoIso/signAction/quotient; no group product/l-torsion/terminal.

Consumer: S1536 SourceSignQuotientGeometricCore/Data -> A/F source-object chain.

Reports read: MAINLINE_ABC_F.md; gap-exploration-20261030.md §备选路线; S1449-report-ABC-graph.md §0; 心得.md; ACTUAL-OBLIGATIONS-CLASSIFICATION.md.

Lean: tmp/sheaf/xif/paper/S1689StackTwoIsoProofActual.lean
EXIT=0; SHA256 91FA51A31675A419348C70BA5B9563BC4492C20AD33FF353EA7872F21D6BD2B9
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1689StackTwoIsoProofActual.olean