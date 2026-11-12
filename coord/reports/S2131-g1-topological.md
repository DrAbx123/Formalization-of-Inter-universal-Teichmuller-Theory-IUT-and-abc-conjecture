# S2131 G1: topological cyclotome module exact surface

Layer: O (S2046 G1).
Source object: muHatZ p = KummerCyclotome(muQZ p), PsiCnsCyclotome p.
Domain: cyclotome modules, G_v-actions.
Direction: actual module equivalence conditional on muHatComparison; topological muHat action exact missing.

BUILT:
- S2131MuHatActionRequired := Gv p →* MulAut (muHatZ p).
- S2131MuHatComparisonRequired := muHatComparison p.
- S2131ModuleEquivOfComparison: actual muHatZ p ≃* PsiCnsCyclotome p from muHatComparison.
- S2131TopologicalModuleData/Required and S2131TopologicalModuleDataOf: conditional actual assembly from action + equivariance.

MISSING exact: the topological G_v-action on muHatZ and its equivariance with S2000's PsiCns coefficient action. muHatComparison p itself also remains an input (M2c/M2b dependent). No fake.

Lean: tmp/sheaf/xif/paper/S2131G1TopologicalActual.lean
EXIT=0; SHA256 B0E887A516A1D2BA74EA8FC64B2C2BB6011F3E879C790AFB258E0DFDCFFD8486
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2131G1TopologicalActual.olean
olean SHA256: 631348347A0B0E81A7455D63C7C8078DDD31924112F030BFC46372AD9F296DFC
axioms: propext, Classical.choice, Quot.sound (no sorryAx).