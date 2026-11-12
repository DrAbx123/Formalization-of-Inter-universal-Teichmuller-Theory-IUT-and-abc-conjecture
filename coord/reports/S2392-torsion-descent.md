# S2392: torsion descent exact surface

Layer: O (S2179 stage compatibility).
Source object: S2179TransferCompatible.
Domain: Stage/toStage/torsion descent.
Direction: exact surface; minimal decomposition mismatch.

MINIMAL GOAL after unfolding S2179StageConj:
- S2179's e' is h ▸ (equivMapOfInjective H (conj g.symm)), while S2200ConjEquiv is e.trans (subgroupCongr h).
- Need Ab.map equality between these two equivalences; simp leaves the h ▸ e coercion vs S2200ConjEquiv form.
- After that, toStage/torsion values agree by S2371_verlagerung_natural pointwise.

BUILT:
- S2392StageDescentRequired = S2179TransferCompatible.

MISSING exact: Ab.map equality between S2179's h ▸ equivMapOfInjective and S2200ConjEquiv, then torsion pointwise. No fake.

Lean: tmp/sheaf/xif/paper/S2392TorsionDescentActual.lean
EXIT=0; SHA256 94C8B9EE2E47093927E8007D77D863A1D336181967915D563AC92677A1BBF09D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2392TorsionDescentActual.olean
olean SHA256: E4205346FFEFCBDBC695BDBA383FB2B490CA201B2EE1F2AEEE9271A743678E40
axioms: none (definition/Prop surface only; no theorem closure).