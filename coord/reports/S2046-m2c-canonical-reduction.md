# S2046 M2c: canonical torsion comparison reduction

Layer: O (S2046 M2c; S2027 abelianization carriers).
Source object: torsionMap of abelianizationToTopological.
Domain: abstract abelianization vs topological abelianization of localGaloisGroup.
Direction: exact canonical map and reduction targets; no proof/counterexample yet.

BUILT:
- S2046M2cCanonicalMap := torsionMap (abelianizationToTopological p U).
- S2046M2cCanonicalComparisonRequired := canonicalTorsionComparison p U.
- S2046M2cInjectivityRequired, S2046M2cSurjectivityRequired.
- S2046M2cCommutatorClosedRequired: closure(commutator) = commutator.
- S2046M2cCommutatorToCanonical: exact implication target from commutator-closed to M2c.

MISSING exact: injectivity of the canonical torsion map (equivalently canonicalTorsionComparison), or the commutator-closed condition plus the implication. No fake/counterexample established.

Notes: S2102 M2a torsion actual; S2104 completion torsion actual; M2c remains independent.

Lean: tmp/sheaf/xif/paper/S2046M2cCanonicalReduction.lean
EXIT=0; SHA256 E6B0CBE929729003E487AE7AB47530B52E540128292A1CBDB8C31B3FA9E1343D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046M2cCanonicalReduction.olean
olean SHA256: 9A66DDCB2B7E2AC0C5A960B800543ECD076FB22143429CAC071345123A604514
axioms: none (definitions/Prop surface only; no theorem closure).