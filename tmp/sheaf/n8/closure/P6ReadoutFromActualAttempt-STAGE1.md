# P6 readout from actual attempt

- Task: Wave6 actual P6L readout attempt.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6ReadoutFromActualAttempt.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorry: 1 (`noAdmissibleGlobalRegion_obligation`).

## Actual data used

- native places `NativePlaces X.S` and `localFieldAt X v`;
- actual local Haar measure `mu` with `IsAddHaarMeasure`;
- actual source-region candidates `unitBall` and `unitSphere`.

The unit sphere has actual local log zero (`unitSphere_localLog_zero`), but its
additive Haar mass is zero, so it cannot satisfy positive-mass Adm.  The unit
ball has positive mass but real local log is not a.e. zero.  No actual
procession weights/dimensions/reference calibration are present.

## Exact no-go

`NoAdmissibleGlobalRegion : Prop := not exists reference region, Adm reference region`.
`noAdmissibleGlobalRegion_obligation` is the theorem-level named sorry.

`noP6Readout_of_noAdmissible` derives from it
`not Nonempty (P6L.P6Readout X mu)`, using the readout's Adm field.

## Target record

`P6ReadoutFromActualTarget := Nonempty (P6L.P6Readout X mu)`.
No actual instance is constructed; no free Real/Set or fake field.

## Status

statement_compiles true; actual local log/region candidates present; actual
P6Readout not constructed; exact no-go named sorry.