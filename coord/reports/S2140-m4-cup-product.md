# S2140 M4 cup-product: exact map surface

Layer: O (S2046 M4).
Source object: PsiCnsCohomology p; H2ZHatOne/Br port; S2112 Z^2 exchange imported.
Domain: actual continuous H^1 limit.
Direction: exact cup-product normalization map surface; no inhabitant.

BUILT:
- S2140H2ZHatEquiv and S2140BrEquivQZ re-export actual S2091 ports.
- S2140CupProductMapRequired := PsiCnsCohomology p →* Multiplicative Zhat.
- S2140SurjectiveNormalizationRequired := subtype of surjective maps.
- S2140CupProductNormalizationRequired := S2136M4NormalizationData p.
- S2140M4_of_data: conditional actual PsiCnsKummerNormalization from the data.

MISSING exact: cup-product normalization map on PsiCnsCohomology with surjectivity/Kummer-image/kernel-units. S2112 Z^2 exchange imported; no M4/M3 assumption; no fake.

Lean: tmp/sheaf/xif/paper/S2140M4CupProductActual.lean
EXIT=0; SHA256 4A08C4638521B7EACAB08A627F85D3309F84BE8884F63608CDAAA93B077091D1
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2140M4CupProductActual.olean
olean SHA256: DA136F443520B412247792CE1798655CCF7D7071CFC401B2E259D11E3750ED22
axioms: propext, Classical.choice, Quot.sound (no sorryAx).