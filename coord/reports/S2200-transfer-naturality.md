# S2200: actual conjugation equivalence of abelianizations; transfer naturality exact missing

Layer: O (transfer naturality).
Source object: S2200ConjEquiv on open subgroups, verlagerungOpen.
Domain: abelianizations and Verlagerung.
Direction: actual canonical group equivalence; conjugation naturality of transfer exact missing.

BUILT:
- S2200ConjEquiv: H ≃* S2169ConjIndex g H, actual via S2173ConjSubgroupEquiv and subgroupCongr.
- S2200TransferNaturalityRequired: exact naturality of Abelianization.map/verlagerungOpen under conjugation.
- S2200TransferCompatRequired, S2200MuQZMulAutRequired exact targets.

MISSING exact: transfer naturality (S2200TransferNaturalityRequired); stage compatibility and MulAut action follow. No fake.

Lean: tmp/sheaf/xif/paper/S2200TransferNaturalityActual.lean
EXIT=0; SHA256 C087E3E816B8EC8A63CB474245CD438EBF14C481D65921D67AAC163284146263
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2200TransferNaturalityActual.olean
olean SHA256: 1FD3DCD9D6537C99FBE157C17112EBFAC828E83F8F41B9FECF66599B580CFE6B
axioms: propext, Classical.choice, Quot.sound (no sorryAx).