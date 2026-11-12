# S2341: Ab.map inclusion compatibility SUCCESS

Layer: O (transfer compatibility).
Source object: Ab.map subgroupOfEquivOfLe and S2200ConjEquiv.
Domain: abelianization of subgroup inclusion.
Direction: PROVED abmap inclusion compatibility.

BUILT:
- S2341_abmap_inclusion:
  (Ab.map eH).comp (Ab.map inclH)
  = (Ab.map inclH').comp (Ab.map eHsub),
  where h' = S2338_conjIndex_mono, hcast = S2317_subgroupOf_map,
  eHsub = equivMapOfInjective Hsub eK trans subgroupCongr hcast.
Proof: Abelianization.hom_ext, ext x, map_of, congr 1.

PROVED: compatibility; axioms trio.

NEXT: substitute into S2336_verlagerungOpen_eq + S2292_transferAb_natural to get S2300VerlagerungNaturalRequired, then S2179.

Lean: tmp/sheaf/xif/paper/S2341AbMapInclusionActual.lean
EXIT=0; SHA256 2A30FAB9B2D51304EE29F273C9E2244B327BEC5C6189FA4860CA271381BBC86E
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2341AbMapInclusionActual.olean
olean SHA256: A08162B8E9FA24FB69BAF1194521187788846BB3833C7898B9E906FFC88039D5
axioms: propext, Classical.choice, Quot.sound (no sorryAx).