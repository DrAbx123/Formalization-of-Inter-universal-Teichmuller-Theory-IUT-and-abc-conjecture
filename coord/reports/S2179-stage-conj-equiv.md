# S2179: actual stage conjugation equivalence

Layer: O (muQZ conjugation).
Source object: Stage p H, open-subgroup conjugation, Abelianization/torsion.
Domain: stage groups.
Direction: actual subgroup identification and actual stage add-equivalence; transfer compatibility is exact missing.

BUILT:
- S2179MapConjEqComap: H.map(conj g.symm) = H.comap(conj g) as subgroups.
- S2179StageConj: Stage p H ≃+ Stage p (S2169ConjIndex p g H), actual via abelianizationCongr/torsionCongr.
- S2179StageConjugationRequired_actual: inhabits S2169StageConjugationRequired.
- S2179TransferCompatible: exact transfer compatibility Prop (no proof/inhabitant).

PROVED: actual stage conjugation equivalence; axioms trio.

MISSING exact: S2179TransferCompatible with toStage/Verlagerung, then colimit descent to muQZ action. No fake.

Lean: tmp/sheaf/xif/paper/S2179StageConjEquivActual.lean
EXIT=0; SHA256 0030AAF0FAFE9FA81C6EF3A2B3F0F0220D1648E95A95161E05FF43D0E5136F12
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2179StageConjEquivActual.olean
olean SHA256: 40EBB1380378FD4E7DFA63C64AFAE74A05BC93DEAFA7B6B7AFB270AB14074515
axioms: propext, Classical.choice, Quot.sound (no sorryAx).