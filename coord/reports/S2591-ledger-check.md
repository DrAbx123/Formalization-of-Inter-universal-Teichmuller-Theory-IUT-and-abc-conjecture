# S2591 / S2564 olean freshness and axiom ledger check

Date: 2026-11-06 (Asia/Shanghai)
Owner: subagent L-C, parent b8ad2096-3f28-4984-a7ee-263d53396072
Stage: verification only. No Lean source was written or modified by this check.
Git HEAD at check time: 9399e9fab4d62ea5f78a4a0d56ceecb84525a3ee.
Snapshot time for the hashes below: 2026-11-06T03:49:42+08:00.

## Targets and method

Actual files found by glob under `tmp/sheaf/xif/paper`:

* `tmp/sheaf/xif/paper/S2591PointLocalLogDegreeActual.lean`
  (declarations `S2591PointLocalLogDegree`, `S2591PointLocalLogDegreeMap`)
* `tmp/sheaf/xif/paper/S2564TauCetiInstanceSkeletonActual.lean`
  (structure `S2564TauCetiInstanceSkeleton` and its surrounding instances)

Freshness was checked by a serial recompile of each source to a temporary
output path, using exactly the prescribed policy command, then comparing the
SHA-256 and size of the produced olean with the installed olean under
`.lake/build/lib/lean/tmp/sheaf/xif/paper/`:

    lake env lean -j1 -DmaxHeartbeats=8000000 -R . -o "<TEMP>/<module>.olean" "<source>"

A byte-identical output means the installed olean is the current source as
compiled against the current on-disk dependency oleans. The temporary oleans
were hashed and then deleted; no installed olean or Lean source was overwritten.
Axiom checks were run serially through
`lake env lean -j1 -DmaxHeartbeats=8000000 -R . --stdin` against the installed
oleans. The sources were also grepped for `sorry`, `admit`, `native_decide`
and `axiom`: 0 hits in both files.

## S2591PointLocalLogDegreeActual

| item | value |
|---|---|
| source | `tmp/sheaf/xif/paper/S2591PointLocalLogDegreeActual.lean` |
| source size | 1479 bytes |
| source SHA256 | `E75CAAC3D0DC375E48CD6ACE9FB432881463CBB8AEE562BBD46B1805E6B00F4B` |
| source mtime | 2026-11-06T03:36:07+08:00 |
| installed olean | `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2591PointLocalLogDegreeActual.olean` |
| olean size | 22544 bytes |
| olean SHA256 | `78FD6108D8125648CDAF93C649E690FA06B8F8B63619921D54EA087E68CFAD2E` |
| olean mtime | 2026-11-06T03:44:02+08:00 |
| fresh recompile | EXIT=0, 77.73 s, temp olean SHA256 `78FD61...CFAD2E`, size 22544 bytes |
| byte-identical to installed olean | yes |
| stale status | NOT STALE |

`#print axioms` (both checks EXIT=0, no `sorryAx`):

* `LeanFormal.IUT.XiFPaper.S2591PointLocalLogDegreeActual.S2591PointLocalLogDegree`
  depends on axioms: [propext, Classical.choice, Quot.sound]
* `LeanFormal.IUT.XiFPaper.S2591PointLocalLogDegreeActual.S2591PointLocalLogDegreeMap`
  depends on axioms: [propext, Classical.choice, Quot.sound]

Note: the installed olean mtime moved from 03:37:03 to 03:44:02 during this
check (an independent rebuild), but its SHA-256 and size did not change.

## S2564TauCetiInstanceSkeletonActual

Final snapshot:

| item | value |
|---|---|
| source | `tmp/sheaf/xif/paper/S2564TauCetiInstanceSkeletonActual.lean` |
| source size | 2900 bytes |
| source SHA256 | `C1A2C8AC68561DC42848535721611C218F726C972684E4B7153075FDDEE012E0` |
| source mtime | 2026-11-06T03:41:09+08:00 |
| installed olean | `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2564TauCetiInstanceSkeletonActual.olean` |
| olean size | 68152 bytes |
| olean SHA256 | `EA5ECDB743E844324F7E27CA210225D50D489D3D6FD21BA3641F3AE95D18A577` |
| olean mtime | 2026-11-06T03:44:43+08:00 |
| fresh recompile | EXIT=0, 81.90 s, temp olean SHA256 `EA5ECD...D18A577`, size 68152 bytes |
| byte-identical to installed olean | yes |
| stale status | NOT STALE |

`#print axioms` on the final olean (all checks EXIT=0, no `sorryAx`):

* `...S2564TauCetiInstanceSkeleton` -> [propext, Classical.choice, Quot.sound]
* `...S2564ValuativeExtensionTarget` -> [propext, Classical.choice, Quot.sound]
* `...S2564FCompletionValuativeRel` -> [propext, Classical.choice, Quot.sound]
* `...S2564BaseCompletionRawValuativeRel` -> [propext, Classical.choice, Quot.sound]
* `...S2564FValuedCompatible` -> [propext, Classical.choice, Quot.sound]
* `...S2564FCompletionIsNontrivial` -> [propext, Classical.choice, Quot.sound]
* `...S2564BaseValuedCompatible` -> [propext, Classical.choice, Quot.sound]
* `...S2564BaseCompletionIsNontrivial` -> [propext, Classical.choice, Quot.sound]

Concurrent update observed during the check: the first snapshot (03:39) had
source 1818 bytes / SHA256 `EA5448CA2595062F1369C50ACAEBE0C6F2C8AAD25B4B7DA25401F8C94A09A9A`
and installed olean 49928 bytes / SHA256
`E80AFA5694965ECC8ED024E075CBBF174B918CC2F1381DC08FFB5B89E1AE56B9`
(mtime 03:35:44, axiom trio). The source was then updated at 03:41:09 to the
2900-byte version above, which adds the two nontriviality instances, and the
installed olean was rebuilt at 03:44:43. All figures and all axiom prints in
this section are from the final current olean; the earlier print was
superseded by the rebuild.

## Verdict

| target | source SHA256 | installed olean SHA256 | olean size | stale | axioms |
|---|---|---|---|---|---|
| S2591PointLocalLogDegreeActual | `E75CAAC3D0DC375E48CD6ACE9FB432881463CBB8AEE562BBD46B1805E6B00F4B` | `78FD6108D8125648CDAF93C649E690FA06B8F8B63619921D54EA087E68CFAD2E` | 22544 B | NO | [propext, Classical.choice, Quot.sound] |
| S2564TauCetiInstanceSkeletonActual | `C1A2C8AC68561DC42848535721611C218F726C972684E4B7153075FDDEE012E0` | `EA5ECDB743E844324F7E27CA210225D50D489D3D6FD21BA3641F3AE95D18A577` | 68152 B | NO | [propext, Classical.choice, Quot.sound] |

Status labels for this check:
statement_compiles: yes (both oleans fresh and byte-identical to serial recompile);
proof_body_checked: not applicable to the definitions/structure declarations as
targets, but the checked declarations are axiom-clean;
kernel_closed: yes for the checked declarations (trio only, no sorryAx);
target_accepted: not claimed by this report.

## Boundary notes

* The S2564 structure is a skeleton of obligations, not an existence result.
  Its fields are `IsNonarchimedeanLocalField ...`, `IsNonarchimedeanLocalField ...`
  and `S2564ValuativeExtensionTarget ...`; this file does not construct a term
  of the structure. `#print axioms` being trio-only does not discharge those
  field obligations.
* Direct local dependency sanity (newer source/olean pairs):
  `S2588RationalPointMapActual` src 03:20:47 -> olean 03:34:39;
  `S2587Cor312PointMapSkeletonActual` src 03:14:30 -> olean 03:19:14;
  `RelativeNormCompletion` src 2026-10-28 13:45:41 -> olean 2026-10-28 15:41:55.
  Mathlib dependency oleans under `.lake/packages/mathlib/.lake/build/lib/lean/`
  are newer than their sources. A full transitive import audit was not performed.
* The repository is under active concurrent work: the S2564 skeleton source
  changed while this check was running. If it is edited again, the freshness
  evidence above applies only to SHA256 `C1A2C8AC...` (2900 bytes).
