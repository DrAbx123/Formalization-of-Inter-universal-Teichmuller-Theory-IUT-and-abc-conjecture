# S2159: muQZ discrete topology and conditional muHat action

Layer: O (G1 topological cyclotome).
Source object: muQZ p, muHatZ p, Gv p.
Domain: topology and action on the group-theoretic cyclotome.
Direction: actual discrete topology; exact missing conjugation action; conditional muHat action.

BUILT:
- S2159MuQZTopology := bottom topology on Multiplicative (muQZ p).
- S2159MuQZDiscrete and S2159MuQZIsTopologicalGroup actual.
- S2159MuQZActionRequired: exact missing action Gv p →* MulAut (Multiplicative (muQZ p)).
- S2159MuHatActionOfMuQZ: actual pointwise action on muHatZ from an algebraic action on muQZ.
- S2159TopologicalModuleDataOf: conditional S2131TopologicalModuleData from action + muHatComparison + equivariance.

MISSING exact: actual conjugation Gv-action on muQZ; continuity/topological compatibility; induced equivariance with PsiCnsCoefficientAction. muHatComparison remains an input. No fake.

Lean: tmp/sheaf/xif/paper/S2159MuQZActionActual.lean
EXIT=0; SHA256 F61DBFB0B5DEFA3242EB18545AFD58798D78F08A0A05EBFAB1E9E172A9328411
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2159MuQZActionActual.olean
olean SHA256: B101B761001FB1B43BC15403F8C9F37325D78513F1A9EEDE1B0416236AFBBA39
axioms: propext, Classical.choice, Quot.sound (no sorryAx).