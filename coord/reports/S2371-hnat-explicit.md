# S2371: hnat explicit and S2300VerlagerungNaturalRequired PROVED

Layer: O (transfer compatibility).
Source object: transferAb naturality for eHsub, final verlagerungOpen square.
Domain: transfer compatibility.
Direction: PROVED S2371_hnat and S2371_verlagerung_natural.

BUILT:
- S2371_hnat: (Ab.map (e0.trans subgroupCongr hcast)).comp (transferAb H) = (transferAb H').comp (Ab.map eK), independent of cases.
- S2371_verlagerung_natural: S2300VerlagerungNaturalRequired, via S2336_verlagerungOpen_eq, S2341_abmap_inclusion, S2371_hnat, comp_assoc.

PROVED: both; axioms propext, Classical.choice, Quot.sound.

NEXT: descend to S2179TransferCompatible via toStage/torsion; then S2189MuQZMulAutData.

Lean: tmp/sheaf/xif/paper/S2371HnatExplicitActual.lean
EXIT=0; SHA256 6D662D266FE63D029EFC0A9BC3453151F3F7326A4E37D26591F82A0CFF5FB35A
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2371HnatExplicitActual.olean
olean SHA256: 1380B17B8E784AE2C85842A1FA142CF946F63B84D6D5E0352BDB27197EDF3EE8
axioms: propext, Classical.choice, Quot.sound (no sorryAx).