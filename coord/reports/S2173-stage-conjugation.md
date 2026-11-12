# S2173: stage conjugation helpers; exact stage equivalence missing

Layer: O (muQZ conjugation).
Source object: Abelianization H, torsion, Stage H, subgroup conjugation.
Domain: stage groups and open-subgroup conjugation.
Direction: actual abelianization/torsion conjugation helpers; open-subgroup image/stage equivalence exact missing.

BUILT:
- abelianizationCongr: Abelianization G ≃* Abelianization H from a MulEquiv.
- torsionCongr: torsion G ≃* torsion H from a MulEquiv.
- S2173ConjSubgroupEquiv: H ≃* H.map (conj g) at the subgroup level.
- S2173StageConjugationRequired: exact missing stage conjugation at S2169ConjIndex.

MISSING exact: identify H.map (conj g) with S2169ConjIndex g H as an OpenSubgroup, then transport torsionCongr/abelianizationCongr to Stage and prove transfer compatibility. No fake.

Lean: tmp/sheaf/xif/paper/S2173StageConjugationActual.lean
EXIT=0; SHA256 F0D09FDC6A76E640C07B3FB835353E9D4F0B10C56348FEAA2A896C32D61E2A4D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2173StageConjugationActual.olean
olean SHA256: 6518772968249294A57C9243B21E16E0F10A3F89883E9FE0580E47B1771BE3E1
axioms: propext, Classical.choice, Quot.sound (no sorryAx).