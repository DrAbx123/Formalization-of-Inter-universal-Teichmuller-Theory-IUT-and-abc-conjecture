# Actual corrected global relaxed P6 readout

- Task: Wave31.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6RelaxedGlobalReadoutActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0, no sorry.

## Construction

`relaxedGlobalReadoutActual hultra hproperFinite hproperArch`
  : `P6RelaxedGlobalReadout.RelaxedGlobalReadout X mu` with
- finite := actual `relaxedFiniteReadout`: nonarch unit sphere reference/region,
  actual residue-cardinality weights/dimensions, singleton bad-finite support;
- arch := actual `archReadout`: archimedean closed unit ball reference/region,
  actual base infinite-place multiplicity weights/dimension, actual ell_out.

No arbitrary region: finite uses `unitSphereAt`, arch uses `archClosedBall`.

## Replacement

`relaxedGlobalReadoutActual_nonempty` gives `Nonempty (RelaxedGlobalReadout X mu)`
from the actual components, replacing the former `missing_archReadout` named
gap.  `relaxedGlobalReadoutActual_regions_actual` records the actual nonempty
finite support.

## Status

statement_compiles true; proof_body_checked true for this construction; no
sorry in this file.  Upstream `P6RelaxedGlobalReadout.missing_archReadout` still
exists as a named sorry, but the actual replacement declaration is here.