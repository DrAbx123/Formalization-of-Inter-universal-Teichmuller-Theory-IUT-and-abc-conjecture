# P6-L closure: global readout + Chain A/B source existence

- Task: P6LClosure, strict current N8 line.
- Owner: logdescent.
- Lean: tmp/sheaf/n8/closure/P6LClosure.lean.
- Compile: lake env lean -j1 -R D:/lean -> EXIT=0.
- Named sorries: 2 (`p6LSourceGap_obligation`, `p6LSourceClosure_nonempty`).
- No old L0.5 target used.

## Reused interfaces

- P6L: `P6Readout`, `ellOut`, global `Adm`; global L is a finite-support
  place-indexed sum, not a single block normalizedLogVolume.
- P6ChainA: `P6ChainAData`, `GlobalLqDonor`; Q tied to L_q.
- P6ChainB: `CompleteAlpha`, `RAlpha`, `MissingSLToCompleteAlpha`.

## Declarations

- `P6LSourceGap : Prop`
  := `Nonempty (P6Readout X mu) ∧ Nonempty (GlobalLqDonor X) ∧
      MissingSLToCompleteAlpha X`.
  Exact existing P6L/P6ChainA/P6ChainB targets; no new types.
- `p6LSourceGap_obligation : P6LSourceGap X mu` -- named sorry.
- `P6LSourceClosure` structure: `readout : P6Readout`, `chainA :
  P6ChainAData X`, `chainB : CompleteAlpha D`.  All existing interface types;
  no free Real/Set field.
- `P6LSourceClosure.ofData` actual constructor from supplied components.
- `P6LSourceClosure.readout_value_eq`: readout value equals P6L `ellOut`.
- `P6LSourceClosure.chainA_Q_eq`: Chain A Q projection.
- `P6LSourceClosure.chainB_RAlpha_eq`: Chain B R_alpha equals actual D.U.
- `p6LSourceClosure_nonempty : Nonempty (P6LSourceClosure ...)` -- named sorry.

## Gap

Named sorry records the exact source existence gap: an actual global P6
readout/Adm region family and complete-alpha construction are missing.  No
single-block normalizedLogVolume proxy is used; no old L0.5 target is imported.

## Status

statement_compiles true; P6L/ChainA/ChainB interfaces wired; source existence
is named-sorry only; not math closed.