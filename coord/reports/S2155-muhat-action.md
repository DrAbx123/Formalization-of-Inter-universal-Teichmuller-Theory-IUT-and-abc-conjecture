# S2155 muHat action: exact missing surface

Layer: O (S2046 G1 topological cyclotome).
Source object: muHatZ p, muQZ p, Gv p.
Domain: topological G_v-module structure on muQZ/muHatZ.
Direction: exact missing topology/action; conditional G1 data assembly.

BUILT:
- S2155MuQZTopologyRequired := TopologicalSpace (Multiplicative (muQZ p)).
- S2155MuQZActionRequired := Gv p →* MulAut (Multiplicative (muQZ p)).
- S2155MuHatActionRequired := Gv p →* MulAut (muHatZ p).
- S2155MuQZContinuousActionRequired: topology + discrete + action + continuity structure.
- S2155TopologicalModuleDataOf: conditional S2131TopologicalModuleData from action + muHatComparison + equivariance.

MISSING exact: actual topology on muQZ, actual conjugation action on muQZ, its continuity/discreteness, and the induced muHatZ action/equivariance. No M2c/M3 assumption, no fake.

Lean: tmp/sheaf/xif/paper/S2155MuHatActionActual.lean
EXIT=0; SHA256 2E89A1E482EB9854919ABD558C42A77CD18B1B13A4985FF8C5487C4A612D0EEB
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2155MuHatActionActual.olean
olean SHA256: CD352BFBAAA71ADC71223EA36779E33DC09B0D05DCAE787D304EA82E69380066
axioms: propext, Classical.choice, Quot.sound (no sorryAx).