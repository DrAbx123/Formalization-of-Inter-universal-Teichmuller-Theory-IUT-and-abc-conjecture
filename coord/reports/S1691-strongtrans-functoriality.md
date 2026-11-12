# S1691: app-level StrongTrans functoriality actual; full StrongTrans equality missing

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve; S1419AffineOver = Spec R.
Domain: actual representable scheme endomorphism and its StrongTrans app components.
Direction: actual app-level functoriality/id; full StrongTrans equality/TwoIso/nonidentity/signAction exact missing.

BUILT/PROVED:
- S1691App_vcomp: app e ≫ app e = app (e ≫ e) for every scheme endomorphism e.
- S1691App_id: app (identity scheme endo) = identity functor.
- S1691SchemeEndo_sq: scheme endomorphism square = identity (from S1685).
- S1674StackLift remains actual.

MISSING exact:
- S1691StrongTransFunctorialityMissing: vcomp (st e) (st e) = st (e ≫ e).
- S1691StrongTransIdMissing: st identity = identity StrongTrans.
- S1691StackLiftNonidentityRequired.
- S1691SquareTwoIsoRequired.
- OrbicurveSignAction and OrbicurveSignQuotientWitness/quotient.
No fake TwoIso/signAction/quotient; no group product/l-torsion/terminal.

Consumer: S1536 SourceSignQuotientGeometricCore/Data -> A/F source-object chain.

Reports read: MAINLINE_ABC_F.md; gap-exploration-20261030.md §备选路线; S1449-report-ABC-graph.md §0; 心得.md; ACTUAL-OBLIGATIONS-CLASSIFICATION.md.

Lean: tmp/sheaf/xif/paper/S1691StrongTransFunctorialityActual.lean
EXIT=0; SHA256 3AA159B976C4B252F0D8998FA0F9152E88EFDBFB498FFAE1A4E6908A26408A5A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1691StrongTransFunctorialityActual.olean