# MODEL-CORRECTION — completion-root impossibility and L-carrier replacement

Status: **PROVED (unconditional negative theorem) + migration plan**. Date 2026-11-12; lane hull.

## 1. 定理陈述与证据

File: `tmp/sheaf/xif/paper/Mzk1CompletionUnconditionalActual.lean`
(new file; `Mzk1CompletionNoRootActual` excluded/unchanged).

Commands / gate:
- `cd D:\lean; lake env lean -R . -o .lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1CompletionUnconditionalActual.olean tmp/sheaf/xif/paper/Mzk1CompletionUnconditionalActual.lean`
- EXIT=0; fresh olean; `#print axioms` all exactly
  `[propext, Classical.choice, Quot.sound]`.
- File SHA256: `9ABB87A3D663ACC37FC8581C51196A5DEEBBBB62AA38DAF52910C5CD58146A4D`
- Olean SHA256: `440DCA48EE09F61FD62897951EA782EA91B37D8F70E60B73E253D0409DC5A887`

Statements:
1. `no_natRootSystem_of_valExp_pos`
   `(u : (CommonPrimeCompletion place)ˣ) (hpos : 0 < unitValExp place u) :
      ¬ Nonempty (NatRootSystem u)`.
2. `completionFirstFieldObstruction_empty` (for every actual `I`, `place`):
   `¬ completionFirstFieldObstruction (I := I) place`,
   i.e. `¬ Nonempty (NatRootSystem (concreteQUnit ...))`.
3. `actualCompletionRootBlock_empty`:
   `¬ Nonempty (CompletionRootBlock (actualSourcePilotRegionCore place))`.
4. `oldSourcePilotWithActualCore_empty`:
   `¬ OldSourcePilotWithActualCore (I := I) place` — no old
   `SourcePilotRegionData` with the actual core.

Also green (conditional, earlier): `Mzk1CompletionNoRootActual.lean`,
`no_natRootSystem_of_no_sqrt` / `completionFirstFieldObstruction_false_of_no_sqrt`
(EXIT=0/trio; hash `83B317E64B451DBB8A633EA3BC00BA993737B494DE4DC4883C9223ACCAD34FA1`).

## 2. 证明思路

1. **Instance bridge (definitional, no axiom)**:
   `commonPrimeCompletionValued : Valued (CommonPrimeCompletion place)
     (WithZero (Multiplicative ℤ)) :=
     `inferInstanceAs (Valued (Completion place.val) ...)`.
   This is unfolding `CommonPrimeCompletion := NormalizedCompletion := Completion`,
   not an assumption.
2. **Valuation exponent**: `valExpVal` on the value group (`0 ↦ 0`, else
   `-Multiplicative.toAdd (WithZero.unzero _)`), `unitValExp` on units;
   `valExpVal_mul`, `unitValExp_mul`, `unitValExp_pow`;
   `unitValExp_candidateUnits = q.exponent` (with `q.exponent_pos`).
3. **Obstruction**: if `R : NatRootSystem u`, then for every `n ≠ 0`,
   `R.root n ^ n = u` (`NatRootSystem.pow_self`).  Applying valuations gives
   `n * unitValExp (R.root n) = e`, where `e = unitValExp u > 0`.
   Choose `n = e.toNat + 1` (so `n = e+1` in ℤ): then
   `(e+1) * k = e` with `k = unitValExp (R.root n)`.
   From `e > 0` and `n > 0`, `k ≥ 1`, so `(e+1)k ≥ e+1 > e`, contradiction.
4. **Consequences**:
   - `completionFirstFieldObstruction` false (unconditional);
   - `CompletionRootBlock` empty by `actualCompletionRootBlock_nonempty_iff`;
   - `oldSourcePilotWithActualCore_empty` by
     `oldSourcePilotWithActualCore_nonempty_iff`.

## 3. 影响范围

- **Old completion schema is not merely unconstructed — it is impossible**:
  `SourcePilotRegionData`'s first root field requires a `NatRootSystem` on
  `concreteQUnit`, and no such root system exists for any q candidate with
  positive exponent (all actual q candidates have `exponent_pos`).
- **L carrier is forced**: `SourcePilotRegionDataL` (S1391:244,
  `actualSourcePilotRegionDataL` S1391:329) has roots over
  `ConcreteQAlgebraicClosure` and actual Kummer/rootChange towers; it is the only
  constructible C3 source carrier in the current tree.
- **S1408 / old record consumers must migrate**:
  - `sourcePilotRegionDonorsOfLBlock` and `oldSourcePilotOfLBlock` take an old
    `CompletionRootBlock` as explicit input; that input is now provably empty;
  - these consumers are vacuous/legacy and must not be used as evidence for C3;
  - migrate to the L-side consumers (`SourcePilotRegionDataL`, C3 donor fields
    from S1349/S1354, paper q-pilot L object).
- **E1 allocation form**: `Mzk1E1OrderActual`'s `E1AllocationForm`
  (`V_norm = V_hull + qSide`) remains the correct interface; the old-schema
  impossibility does not prove `qSide = 0`, so E1 (bare equality) is not available.
  `E1AllocationForm` reduces to E1 only under `qSide = 0` (`e1_allocation_of_zero`),
  which is still open (A936/E1 verdict).
- **`lana-transitive` 口径**: `Mzk1CompletionUnconditionalActual` imports only
  `Mzk1...S1391` and Mathlib/LeanFormal (no direct lana import beyond the S1391
  transitive closure); its conclusions are conditional-interface/wiring like the
  other paper files and must not be used to support any lana fact.  The negative
  theorem is about the old schema only, not about lana's own objects.

## 4. 迁移计划与下一步

See `coord/OLD-SCHEMA-MIGRATION.md` (worklist; its §1 sketch is now formalized
by this result, update status accordingly).

1. **L-chain gate**: build/gate `SourcePilotRegionDataL` consumers
   (`actualSourcePilotRegionDataL`, S1349/S1354 donor fields, paper L q-pilot).
   Owner: hull; decision point: L carrier + C3 donor fields green.
2. **Class B migration**: retire old `CompletionRootBlock` field from the C3
   donor/source-clause interfaces; replace `sourcePilotRegionDonorsOfLBlock`
   consumers with L-side versions; update `OldSourcePilotWithActualCore` usages to
   record the impossibility lemma.  Owner: stepxi/hull; decision point: no active
   file references the old block as constructible.
3. **E1 decision**: compute the source q order for the concrete l=5 carrier; if
   `q.order ≠ 0`, use `E1AllocationForm` (not bare E1).  Owner: abc/hull;
   decision point: E1 vs allocation form fixed in `Mzk1E1OrderActual`.
