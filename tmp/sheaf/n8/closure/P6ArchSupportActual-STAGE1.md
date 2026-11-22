# Actual nonempty archimedean support

- Task: Wave32 arch support.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ArchSupportActual.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0, no sorry.

## Construction

- `baseInfinitePlace_nonempty`: Mathlib gives a complex embedding and hence an
  infinite place for the number field base.
- `baseInfinitePlace`: actual choice from that instance.
- `archimedeanNativePlace` (Wave19) maps it to a native place.
- `archimedeanNativePlace_not_finite`: the constructed native place is not
  `IsFiniteNativePlace`, so it is an `ArchimedeanPlaces` element.
- `archActualPlace`, `archSupportActual = {archActualPlace}` is an actual
  nonempty finite support.
- `archReadoutNonempty` is an actual `ArchReadout` with this nonempty support,
  actual `InfinitePlace.mult` weights/dimensions, and the actual closed-ball
  Adm.
- `archReadoutNonempty_support` / `archReadoutNonempty_exists` prove nonempty
  support and existence.

No arbitrary support: singleton of the actual native place from the Mathlib
base infinite place.

## Note

The ArchReadout value formula uses the closed-ball reference and region, so the
actual readout value remains zero (reference-relative).  This task fixes the
support emptiness; no arbitrary value is introduced.