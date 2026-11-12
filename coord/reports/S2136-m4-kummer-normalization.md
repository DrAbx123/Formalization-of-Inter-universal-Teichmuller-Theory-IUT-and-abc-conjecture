# S2136 M4: normalization/Kummer-image exact surface

Layer: O (S2046 M4).
Source object: PsiCnsCohomology p, PsiCnsKummer p, H2ZHatOne/Br port.
Domain: actual continuous H^1 limit and Kummer image.
Direction: exact M4 normalization data surface; cup-product map remains missing.

BUILT:
- S2136H2ZHatEquiv := h2ZHatOneEquiv_of_port.
- S2136BrEquivQZ := brEquivQZ.
- S2136M4NormalizationData: norm + surjective + Kummer image + kernel units.
- S2136M4KummerNormalizationRequired := PsiCnsKummerNormalization.
- S2136M4_of_data: actual PsiCnsKummerNormalization from the data.
- S2136M4CupProductNormalizationRequired := the data type.

MISSING exact: the cup-product normalization map on PsiCnsCohomology with surjectivity, Kummer-image equality, kernel-units property. No inhabitant/fake.

Lean: tmp/sheaf/xif/paper/S2136M4KummerNormalizationActual.lean
EXIT=0; SHA256 33D76985B4081548B5B8384703386CBFC4D52764B81698C40207E62080F1DE7A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2136M4KummerNormalizationActual.olean
olean SHA256: DB710568BA2D9BE8DDEC1FB62D12F0A9675FBA1A64F8D6E9BE9310EA9BBCBC44
axioms: propext, Classical.choice, Quot.sound (no sorryAx).