# P6 archimedean Adm no-go

- Task: Wave18 target correction.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ArchimedeanAdmNoGo.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0 (no sorry).

## Actual proof

- `archimedean_unitSphere_mass_zero_mathlib (v) (hv) [NormedSpace R ...]
  [FiniteDimensional R ...] [Nontrivial ...]`
  : `mu v (unitSphere v) = 0`, by Mathlib `Measure.addHaar_sphere` after
  identifying unitSphere with `Metric.sphere 0 1`.
- `localLog_zero_measure_zero_of_sphere_zero`: the local-log-zero set is
  contained in `unitSphere ∪ {0}`, and `measure_singleton` (NullSingletonClass)
  gives measure zero.
- `no_pos_ae_localLog_zero_of_sphere_zero`: positive-mass region with a.e.
  zero local log is impossible (a.e. subset of a null set).
- `noAdm_of_archimedean_at`: no global Adm pair at an archimedean native place.
- `noP6Readout_of_archimedean_at`: no P6L.P6Readout at an archimedean native
  place.

## Status

statement_compiles true; proof_body_checked true for this target correction;
no sorry.  This establishes that any P6 Adm/P6Readout must exclude
archimedean native places; no arbitrary data or old L0.5 target.