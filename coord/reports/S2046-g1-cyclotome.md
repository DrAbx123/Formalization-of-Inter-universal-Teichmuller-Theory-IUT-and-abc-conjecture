# S2046 G1: cyclotome module comparison and exact topological action surface

Layer: O (S2046 G1 / S2000-S2017-S2039 cyclotome).
Source object: muHatZ p = KummerCyclotome(muQZ p), PsiCnsCyclotome p, actual Gv action.
Domain: cyclotome modules and their G_v-actions.
Direction: actual module equivalence from muHatComparison; exact topological G_v-module action missing.

BUILT:
- S2046G1MuHatComparisonRequired := muHatComparison p.
- S2046G1ModuleEquivOfComparison: actual muHatZ p ≃* PsiCnsCyclotome p from muHatComparison (S2039).
- S2046G1PsiCnsAction := (PsiCnsCoefficientAction p).automorphism, actual.
- S2046G1TopologicalModuleData / Required: exact structure with missing muHatAction + equivariance.
- S2046G1TorsionEquiv := PsiCnsCyclotomeTorsionEquiv, actual.

PROVED: module equivalence conditional on muHatComparison and torsion equivalence; axioms trio.

MISSING exact: G1 topological G_v-action on muHatZ and its equivariance/topological module comparison. G2 = PsiCnsH2LimitComparison; G3 = lim1 H1(Gv,mu_n)=0. No fake.

Consumer: S2046 M3/M4; S2091 H2 port.

Lean: tmp/sheaf/xif/paper/S2046G1CyclotomeActual.lean
EXIT=0; SHA256 C664AC7D205A621B4CAE924F373F4448CAFB048F5BCA662EE569379195F2A8CA
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046G1CyclotomeActual.olean
olean SHA256: 8112EEE3738F8370B613C2A3DDB81C5D568D4A7A40A55C5205EBCAF648FC9FC0
axioms: propext, Classical.choice, Quot.sound (no sorryAx).