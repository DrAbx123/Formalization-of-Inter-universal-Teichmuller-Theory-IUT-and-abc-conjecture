# S2169: Gv conjugation on open subgroups; muQZ action exact missing

Layer: O (G1 / muQZ conjugation).
Source object: Gv p acting on Index p by conjugation; muQZ colimit.
Domain: open subgroup lattice, stages, transfer.
Direction: actual conjugation permutation; stage equivalences/transfer/action remain exact missing.

BUILT:
- S2169ConjIndex: actual H ↦ gHg⁻¹ on open subgroups.
- S2169StageConjugationRequired: exact missing Stage H ≃+ Stage (gHg⁻¹).
- S2169TransferCompatible: exact compatibility with toStage/verlagerung.
- S2169MuQZActionData/Required: exact action data with action_compat on colimit generators.

MISSING exact: stage conjugation equivalences, transfer compatibility, descent to muQZ, and MulAut action. No fake.

Lean: tmp/sheaf/xif/paper/S2169MuQZConjugationActual.lean
EXIT=0; SHA256 249A04AAC1845E8E97614C26117346251F35C3E7885704993B10F133F53A2DD6
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2169MuQZConjugationActual.olean
olean SHA256: F4FAAEE3B9D6AB766409F9E5A9A98834401D97A19D27AC533B1DEF9EC5392187
axioms: propext, Classical.choice, Quot.sound (no sorryAx).