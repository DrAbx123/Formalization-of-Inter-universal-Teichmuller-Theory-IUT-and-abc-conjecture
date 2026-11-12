# S2046 M4: conditional port from S2036 normalization to local units

Layer: O (S2046 M4 / S2036 actual PsiCns M234).
Source object: S2036 PsiCnsKummerNormalization and S2090 unconditional local integral units.
Domain: actual local O^x units and normalization inverse image.
Direction: conditional actual reduction; M2/M3/M4 propositions remain exact missing hypotheses.

BUILT:
- S2046M2LocalArtinRequired := M2FirstMissing p.
- S2046M3H2Required := PsiCnsH2Normalization p.
- S2046M4KummerNormalizationRequired := PsiCnsKummerNormalization p.
- S2046M4NormalizationOfKummer: actual surjective normalization from M4 hypothesis.
- S2046M4OtriUnitsEquivNormalization: (Otri p)^x ≃* units of normalization inverse image.
- S2046M4LocalUnitsEquivNormalization: LocalOFieldUnits p ≃* units of normalization inverse image, using S2090 S2046LocalUnitsEquivOtriUnits.
- S2046M4_sufficient: Nonempty form.
- S2046ZhatNonnegEqNatMonoid: exact comparison between S2036 zhatNatMonoid and S2039 zhatNonneg.

PROVED: conditional actual M4 reduction; axioms propext/Classical.choice/Quot.sound.

MISSING exact: M2 local Artin, M3 H^2=Zhat, M4 normalization/Kummer image (S2036), zhatNatMonoid=zhatNonneg comparison, G_v-action on PsiCns units, PsiCns->PsiGau evaluation. No fake.

Consumer: S2046 (b)/(c); S2046PsiCnsActualComponents conditional data.

Lean: tmp/sheaf/xif/paper/S2046M4ConditionalActual.lean
EXIT=0; SHA256 E25C343F9D3B11B7140958A8C50E3ADB145A82F3C7521C024B02847A6B053236
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046M4ConditionalActual.olean
olean SHA256: 8DB873B996ABB23DD419961071049055D5D0A74CE13F11600CAEADD8C95D264A
axioms: propext, Classical.choice, Quot.sound (no sorryAx).