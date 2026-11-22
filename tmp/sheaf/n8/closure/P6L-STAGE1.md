# P6-L: global signed procession-normalized L/ell_out and Adm

- Task: N8 P6-L.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6L.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- One named sorry: `p6ReadoutExists_obligation`.

## Global carrier/region

`GlobalCarrier X := forall v : NativePlaces X.S, localFieldAt X v`.
`GlobalRegion X := forall v : NativePlaces X.S, Set (localFieldAt X v)`.

The global object is a place-indexed family, not one arithmetic tensor block.

## Adm

`Adm reference region` requires for both reference and region:
- local measurability at every native place;
- positive and finite local Haar mass;
- almost-everywhere zero local log `Real.log ‖x‖`.
No pointwise equality to a reference unit region is used.

## Global L / ell_out

`ellOut support weight dimension reference region`
`:= support.sum (fun v => weight v *
     ((log ((mu v (region v)).toReal) - log ((mu v (reference v)).toReal)) / dimension v))`

This is a finite-support sum over native places with procession weights and
dimensions.  It is not a single-block `normalizedLogVolume`.

## P6 readout interface

`P6Readout` contains exact global data: support, weight, nonzero dimension,
reference region, region, `Adm` proof, and a value equal to `ellOut`.
`P6Readout.ellOutValue` projects the signed global readout.

## Missing donor

`p6ReadoutExists : Prop := Nonempty (P6Readout ...)`.
`p6ReadoutExists_obligation` is the theorem-level named sorry: there is no
actual global admissible region family with construction of procession
weights/dimensions and reference calibration in the tree.  No fake data or
free Type/True placeholder is added.

## Status

statement_compiles true; L/ell_out and Adm interface actual; existence donor
named sorry; no single-block proxy used.