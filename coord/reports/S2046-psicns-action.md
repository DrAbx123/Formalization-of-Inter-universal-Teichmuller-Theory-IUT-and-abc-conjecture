# S2046 (b): conditional actual PsiCns units / M4 reduction

Layer: O (IUT II Cor 4.10(ii)).
Source object: S2039 actual Psi_cns = inverse image of zhatNonneg; OtriFv = nonzero integral monoid of F_v.
Domain: actual S2039 PsiCns and local O^tri units.
Direction: conditional actual units equivalence from NormalizationIsValuation + PsiCnsExhaustion; exact local O^x bridge and M4 normalization remain missing.

BUILT:
- S2046PsiCnsUnitsEquivOtriFv(N,hval,hex): (PsiCns N)^x ≃* (OtriFv)^x, actual via S2039 PsiCns_equiv_otriFv and Units.mapEquiv.
- S2046LocalToOtriFvRequired: exact missing local O^x ≃* (OtriFv)^x.
- S2046LocalToPsiCnsOfBridge: conditional actual local O^x ≃* PsiCnsUnits from the bridge + S2039 normalization/exhaustion.
- S2046M4NormalizationRequired and S2046M4_sufficient: M4 exact missing; the S2039 pair suffices.
- S2046M4_of_cor110b: Cor110bKummerIdentification gives the units equivalence.

PROVED: the conditional units equivalence and conditional local-to-PsiCns reduction; axioms propext/Classical.choice/Quot.sound.

MISSING exact: S2046LocalToOtriFvRequired (M1 local-model bridge), M4 normalization/H^2=Zhat, G_v-action on PsiCns units, PsiCns→Gau evaluation map. No fake.

Consumer: S2046 (b)/(c); S2045OperationKummerData after bridge.

Reports read: S2039 actual PsiCns source/report; S2060 carrier correction; S2061/S2064 Galois data.

Lean: tmp/sheaf/xif/paper/S2046PsiCnsActionActual.lean
EXIT=0; SHA256 C7E2E8A8BBF6F352CCB10C1B445C3C90C6D71DB8B11A95602F63C698C224D39C
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046PsiCnsActionActual.olean
olean SHA256: 441C786874F28DB1804A15BC61845B9A3D83E8E2AC308E43D06BFFEA9151F30E
axioms: propext, Classical.choice, Quot.sound (no sorryAx).