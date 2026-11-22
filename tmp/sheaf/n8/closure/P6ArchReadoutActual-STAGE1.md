# Actual ArchReadout

- Task: Wave30.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ArchReadoutActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0, no sorry.

## Construction

`archBaseInfinitePlace (v : ArchimedeanPlaces X)` extracts the base infinite
place from the native index (the `IsFiniteNativePlace` negation).

- `archWeight v := (InfinitePlace.mult base : Real)`;
- `archDimension v := (InfinitePlace.mult base : Real)`;
- `archDimension_ne_zero` from `InfinitePlace.mult_coe_ne_zero`;
- `archEllOut support` is the actual finite-sum ell_out with the actual
  closed-ball reference/region;
- `archReadout hproperArch : ArchReadout X mu` with actual closed-ball Adm,
  actual weights/dimensions, actual ell_out value; support is the actual empty
  finite support;
- `missing_archReadout_actual : Nonempty (ArchReadout X mu)`.

No arbitrary region: reference/region are `archClosedBall` (closed unit ball).
Weights/dimensions are actual base infinite-place multiplicity, not all-ones.

## Upstream

`P6RelaxedGlobalReadout.lean` had two proof errors in `archAdm_closedBall`
(`rw [show ...]` failed); they were fixed by `change` of the actual closed-ball
goal, and the file builds with its old `missing_archReadout` named sorry still
present.  `P6ArchReadoutActual.missing_archReadout_actual` is the actual
replacement declaration.