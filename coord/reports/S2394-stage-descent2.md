# S2394: stage descent second attempt exact surface

Layer: O (S2179 stage compatibility).
Source object: S2179TransferCompatible.
Domain: Stage/toStage/torsion descent.
Direction: exact surface; dependent elimination on S2179MapConjEqComap fails.

MINIMAL FAILURE:
- Attempted S2394_stageConj_eq: S2179StageConj = torsionCongr(abelianizationCongr S2200ConjEquiv).
- After rw [S2179StageConj, S2200ConjEquiv], cases (S2179MapConjEqComap p g H) fails: Dependent elimination failed because the equation proof is used in the h ▸ e cast.
- Need a generalized/explicit equality variable or Subtype.ext proof of the two group equivalences.

BUILT:
- S2394StageDescentRequired = S2179TransferCompatible.

MISSING exact: Ab.map equality of S2179's h ▸ e and S2200ConjEquiv, then torsion pointwise. No fake.

Lean: tmp/sheaf/xif/paper/S2394StageDescent2Actual.lean
EXIT=0; SHA256 7D11C3766779E86465F9830064C54BC068D00D6ADA2DB69D05991A07803D8846
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2394StageDescent2Actual.olean
olean SHA256: 871E0551BADC2305E78AE90FEFECAB7C8F2B156A7D774D867A54460A9A4ED512
axioms: none (definition/Prop surface only; no theorem closure).