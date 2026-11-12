# S2046: component reduction of the operation Kummer/evaluation data

Layer: O (IUT II Cor 4.10(ii) operation Kummer/evaluation; A/F source-object base).
Source object: S2045 actual local O^x/O^xmu carrier and S1973 psiEvaluation layer.
Domain: actual local field at each S1895 place and Psi_env/Psi_gau.
Direction: actual component reduction; (a)/(b)/(c) comparison components exact missing.

BUILT:
- S2046LocalUnits/Action/O^xmu/nontriviality from S2045 actual local carrier.
- S2046PsiEvaluationEquiv : PsiEnvModel v ≃* PsiGauModel v l actual.
- S2046OperationKummerDataOfComponents: conditional actual assembly of S2045OperationKummerData from (a) Galois Equiv, (b) local-to-Psi equiv + action compatibility, (c) local-to-Gau equiv + evaluation compatibility.

PROVED:
- Actual local O^x/O^xmu action and nontriviality.
- Actual psiEvaluation monoid equivalence.
- Conditional component assembly typechecks.
- Axioms: propext, Classical.choice, Quot.sound (no sorryAx).

MISSING exact:
- S2046GaloisEquivRequired: LocalAbsoluteGalois v.1 ≃* Gv v (different completion models Base(QPlace v) vs Q_p; no defeq).
- S2046LocalToPsiRequired + action compatibility: actual LocalO^x ≃* PsiCnsUnits.
- S2046LocalToGauRequired + evaluation compatibility: actual LocalO^x ≃* (PsiGauModel)^x.
No S1487/Q_p model substitution; no fake inhabitant.

Consumer: S2045OperationKummerData and IUT II Cor 4.10(ii); S1973 psiEvaluation/S1951 reduced square downstream.

Reports read: S2045 report; S1973/S1978/S1951 sources; coord/MAINLINE_ABC_F.md.

Lean: tmp/sheaf/xif/paper/S2046OperationComponentsActual.lean
EXIT=0; SHA256 B96E8593807EE20B80409ED69564564BA39FFF1EA7139060AC5C26F5500155EC
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046OperationComponentsActual.olean
axioms: propext, Classical.choice, Quot.sound.