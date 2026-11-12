# S2343: transferAb naturality at hom level

Layer: O (transfer compatibility).
Source object: transferAb naturality as a hom equality.
Domain: abelianization transfer.
Direction: actual hom naturality; S2300 composition still exact.

BUILT:
- S2343_transferAb_natural_hom:
  (Ab.map eHsub).comp (transferAb H) = (transferAb H.map e).comp (Ab.map e).
- S2343VerlagerungNaturalRequired, S2343StageCompatibleRequired exact aliases.

PROVED: hom naturality from S2292 pointwise theorem; axioms trio.

MISSING exact: compose S2336_verlagerungOpen_eq + S2341_abmap_inclusion + S2343_transferAb_natural_hom into S2300; handle subgroupCongr target cast. No fake.

Lean: tmp/sheaf/xif/paper/S2343VerlagerungNaturalDoneActual.lean
EXIT=0; SHA256 3A78A8182C41FF1BB3585DEB0DDFCFA888B0E81A2541229E48934E7571AEF420
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2343VerlagerungNaturalDoneActual.olean
olean SHA256: 09003AD3C3DBA6C909EED501A4BB867474DEE146C0EFF0B97A4105CC976F2476
axioms: propext, Classical.choice, Quot.sound (no sorryAx).