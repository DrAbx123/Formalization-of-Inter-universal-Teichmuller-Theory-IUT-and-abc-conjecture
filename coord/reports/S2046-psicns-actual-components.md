# S2046 components (b)/(c): actual S2039 PsiCns carrier; exact missing interface

Layer: O (IUT II Cor 4.10(ii) operation Kummer/evaluation).
Source object: S2039 actual Psi_cns = inverse image of zhatNonneg under normalization; S2045 actual local O^x.
Domain: S2039 cohomological Psi_cns and S2045 local units.
Direction: exact-missing interface on actual Psi_cns; no IndIntegralMonoid/SourceMLF model.

BUILT:
- S2046PsiCns, S2046PsiCnsUnits: actual S2039 Psi_cns monoid and its unit group.
- Exact S2046PsiCnsNormalizationRequired = PsiCnsNormalization v.1 (M4).
- Exact S2046LocalToPsiCnsRequired (N): S2045LocalUnits v ≃* (PsiCns v.1 N)^x.
- Exact S2046PsiCnsUnitActionData and action compatibility.
- Exact S2046LocalToGauRequired and S2046PsiToGauRequired + evaluation compatibility.
- S2046ActualPsiCnsOperationData / Required: conditional assembly of all missing components.

MISSING exact: M4 normalization (S2039 PsiCnsNormalization), local O^x-to-PsiCns group equivalence, G_v-action on PsiCns units, local-to-Gau comparison, and PsiCns-to-Gau evaluation map.  No inhabitant asserted; no fake.

Consumer: S2045OperationKummerData components (b)/(c); S2046 component assembly.

Reports read: S2039 actual PsiCns report/source; S2045/S2046 sources; S2060 carrier correction (integral units, not all-units).

Lean: tmp/sheaf/xif/paper/S2046PsiCnsActualComponents.lean
EXIT=0; SHA256 BC25BF0A04E65B0E9D76DC192ECE4AA4B1E9F00090825DE56601597002A9E583
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046PsiCnsActualComponents.olean
axioms: none (file contains only definitions/types; no theorem closure).