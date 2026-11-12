# S1653: source object base — orbicurve stack lift

Layer: O / A-F source-object base (D6 sign-quotient xF geometry).
Source object: S1536XF = S1419Orbicurve over S1280 F, with the actual S1348 affine coordinate ring R = K[x,y]/(y^2+xy-x^3-5).
Domain: S1348 Gaussian affine curve scheme/coordinate ring and the S1419 represented etale stack; no cover category, no group product, no l-torsion.
Direction: actual construction (partial): coordinate [-1] endomorphism built; stack StrongTrans lift missing.

BUILT:
- S1653PolyEndo : Rpoly ->_K Rpoly, x |-> x, y |-> -x-y.
- S1653PolyEndo_affinePolynomial: the endomorphism preserves the Gaussian Weierstrass polynomial.
- S1653CoordEndo : R ->_K R, the induced actual algebra endomorphism of the affine coordinate ring.
- S1653IdentityHom : xF.Hom xF, the actual identity endomorphism.
- Exact types S1653MissingStrongTrans / S1653MissingEndomorphism, S1653SignActionRequired, S1653SignQuotientRequired.

PROVED:
- S1653PolyEndo_affinePolynomial.
- S1653PolyEndo_mem_ideal and the quotient lift S1653CoordEndo are well-defined.
- S1653MissingEndomorphism_eq: S1653MissingEndomorphism = S1536FirstMissingField.
- Identity Hom exists (not the involution).

MISSING:
- Nontrivial actual stack lift (StrongTrans) of the coordinate [-1] endomorphism to S1536XF.Hom S1536XF.
- TwoIso(square, id) and uniqueness of that lift.
- OrbicurveSignAction on S1536XF and OrbicurveSignQuotientWitness/quotient.
No fake StrongTrans, signAction, or quotient is inserted; only exact missing types are recorded.

Consumer: S1536 SourceSignQuotientGeometricCore/Data (xF, ellipticInvolution, signAction, quotient); downstream A/F source-object chain.

Reports read:
- D:/lean/coord/MAINLINE_ABC_F.md
- D:/lean/coord/reports/gap-exploration-20261030.md (备选路线 A/B/C/F)
- D:/lean/coord/reports/S1449-report-ABC-graph.md §0
- D:/lean/心得.md
- D:/lean/coord/ACTUAL-OBLIGATIONS-CLASSIFICATION.md

Lean: tmp/sheaf/xif/paper/S1653OrbicurveStackLiftActual.lean
EXIT=0; SHA256 D600CF3AFC74773F302040AFB88009E87B117F3068FD462286424EC62928FAE9
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1653OrbicurveStackLiftActual.olean

No arbitrary Hom, no Shrink/ULift, no group product, no l-torsion, no terminal/fake carrier. Missing is honest.