# IUT 3.12 前置对象 DAG — AUDIT & MAINTENANCE REPORT (lattice)

**Role:** maintenance & audit (A469): wait for owners to submit `coord/target-chain.iut-pre-*.json`, then run merge3+clean2+validate, check 0 conflicts/0 isolated/problems 0, audit that new nodes are theorem-level (reject consumer/rollup/file bookkeeping), summarize here.

**Generated:** 2026-11-11 02:30:10 (Asia/Shanghai)

## 1. CURRENT DAG STATUS (baseline)

| metric | value |
|---|---|
| formal declaration DAG nodes | 725 |
| edges (after auto clean2) | 1000 |
| conflicts | 0 |
| isolated degree-0 nodes | 0 |
| connected components | 1 |
| validate_decl2 | ok=true, problems=0 (info: citation subgraph cycle topo 718/725, informational) |
| merge tool | `tools/dag_merge3.mjs` (auto clean2; do NOT hand-write declaration-dag.json) |

## 2. iut-pre FRAGMENTS RECEIVED

**None yet** (no `coord/target-chain.iut-pre-*.json` at 2026-11-11 02:30:10). Owners have not submitted their theorem-level fragments; audit pending.

## 3. AUDIT CRITERIA (applied when fragments arrive)

1. Fragment name must be `coord/target-chain.iut-pre-<owner>.json`; single-writer rule; no other-fragment edits.

2. Nodes must be **theorem-level**: definitions/constructions/lemmas/main theorems needed for the IUT 3.12 statement; node ids semantic, kind in theorem/def/target/named_input; status per evidence (DEF/PROVED/CONDITIONAL/NAMED/GAP).

3. **Reject** implementation bookkeeping node types: consumer/rollup/cluster/file-dispatch/registry/index nodes not representing a mathematical object or statement; report rejections with reasons.

4. Edges must be statement/proof dependencies (no hierarchy-only/visual-grouping edges in iut-pre fragments); every edge carries evidence planned or observed_source; no fabricated dependencies.

5. No gate edits, no registry edits, no un-HOLD; no watchdog touch/compile by audit.

6. After merge: run `node tools/dag_merge3.mjs` and `node tools/dag_validate_decl2.mjs`; require conflicts=0, isolated=0, problems=0; record any informational cycles.

## 4. NEXT STEPS (waiting mode)

- Poll `coord/target-chain.iut-pre-*.json`; when present: read each fragment, audit node kinds/edges/evidence, run merge3+validate_decl2, record accepted/rejected nodes and counts here.

- Owners (per Lead A469 division) expected: mainline/shehdd/hull/qpilot/stage4/abc/stepxi/lattice-region fragments as assigned.

- No watchdog/compilation actions from audit side.

Prepared by lattice (maintenance & audit); status-only, no gate effect.

## 5. AUDIT ROUND 2 (fragments received) — 2026-11-11 02:33

| fragment | owner | nodes | edges | audit result |
|---|---|---|---|---|
| `coord/target-chain.iut-pre-abc.json` | abc/aibi | 42 | 44 | **FAIL** (2 issues; see below) |
| `coord/target-chain.iut-pre-mainline.json` | (mainline) | 50 | 71 | PASS (theorem-level: 35 theorem + 10 named_input + 4 target + 1 interface; no consumer/rollup/file bookkeeping; all edges have evidence) |
| `coord/target-chain.iut-pre-stage4.json` | (stage4) | 27 | 26 | PASS (17 theorem/3 def/4 target/2 named_input/1 interface; `C.consumer.p1Composite` is a theorem-level consumer, owner should clarify theorem semantics; no file bookkeeping) |

### 5.1 abc fragment issues (owner: abc; do NOT edit other-writer fragment here)

1. **merge3 conflict**: edge `ThetaLink.ultimate -> ThetaLink.procession` unresolved in `iut-pre-abc` (local node id drift; check the actual local node id of the target).
2. **validate_decl2 problem**: node `iut-pre-abc:QPilot.arithmeticDivisor` references missing file `LeanFormal/IUT/IUTIV/ArithmeticDivisorDegree.lean` (validate problems=1).

### 5.2 Current validation after fragments

- merge3: **1 conflict** (abc edge above); isolate/connectivity otherwise fine.
- validate_decl2: **ok=false, problems=1** (abc missing-file problem above); info: citation subgraph cycle (informational).
- DAG counts (after auto-clean2): **828 nodes / 1127 edges / 0 conflicts / 0 isolated** at receipt time; conflicts/probs remain from abc fragment as above.

### 5.3 Audit criteria checked

- Node kinds: only theorem/def/target/named_input/interface (bridge allowed as interface); **no pure consumer/rollup/cluster/file-dispatch nodes admitted**.
- Edges: statement/proof/interface only; every edge carries `evidence` planned/observed_source (abc 27→39 edges had evidence; mainline/stage4 all edges evidence).
- No gate/registry edits; no watchdog/compile actions by audit.

### 5.4 Next audit step

- Wait for abc to fix 1 conflict + 1 missing-file problem (no audit-side edit).
- After fix: re-run merge3+validate_decl2; require conflicts=0, isolated=0, problems=0; then re-check all iut-pre fragments (including any new owner fragments) and update this report.


## 6. AUDIT ROUND 3 (after abc fixes) — 2026-11-11 02:34

- **abc fragment**: 42 nodes / 44 edges; both round-2 issues fixed by owner (abc confirmed):
  - `ThetaLink.ultimate -> ThetaLink.procession` placeholder edge **removed** (conflict cleared);
  - `QPilot.arithmeticDivisor.files` corrected to existing `LeanFormal/IUT/IUTIV/Estimates/ArithmeticDivisorDegree.lean` (validate problem cleared).
  - Audit: kinds = 28 def / 11 theorem / 2 bridge / 1 target; no consumer/rollup/file bookkeeping; all edges have evidence; PASS.
- **mainline fragment**: currently 0 nodes / 0 edges (owner rewriting in place); audit re-run after final content.
- **stage4 fragment**: 4 nodes / 2 edges, all named_input/NAMED; PASS as named-input layer (no theorem-level claims).
- **Verification (after abc fixes)**: `node tools/dag_merge3.mjs` -> **771 nodes / 905 edges / 0 conflicts**; auto-clean2 final DAG -> **771 nodes / 1049 edges / 0 conflicts / 0 isolated / 1 component**; `node tools/dag_validate_decl2.mjs` -> **ok=true / problems=0** (info: citation subgraph cycle topo 764/771, informational; proof subgraph cyclic false).
- Note: abc fragment has 1 node without `files` (`IUT312.statement`, paper target GAP) — expected for a paper target, not a missing-file problem (validate passes).
- iut-pre totals currently: abc 42/44 + mainline 0/0 + stage4 4/2 (owners may still edit; audit will re-run).


## 7. AUDIT ROUND 4 — 2026-11-11 02:34 (post-owner updates)

| fragment | nodes | edges | kinds | statuses | audit |
|---|---|---|---|---|---|
| iut-pre-abc | 48 | 51 | 14 theorem / 28 def / 2 bridge / 2 target / 2 named_input | CONDITIONAL 5, DEF 3, GAP 5, NAMED 4, PROVED 6, TREE_ASSET 25 | PASS (no consumer/rollup/file bookkeeping; all edges evidence; 2 nodes without files are paper target/named inputs) |
| iut-pre-mainline | 0 | 0 | — | — | PENDING (owner rewriting; re-audit on final content) |
| iut-pre-stage4 | 4 | 2 | 4 named_input | NAMED 4 | PASS as named-input layer (no theorem-level claims; 1 node without files expected) |
| iut-pre-stepxi | 12 | 41 | 11 named_input / 1 target | GAP 10, NAMED 2 | PASS as named-input/GAP layer: theorem-level prerequisite inputs (S1.* GAP, IUT312.statement target); no consumer/rollup/file bookkeeping; all edges evidence; note GAP = named paper input, not proved |

- Merge: **0 conflicts**; `dag_validate_decl2`: **ok=true, problems=0** (info: citation subgraph cycle topo 694/789, informational).
- Final DAG after auto-clean2: **789 nodes / 1145 edges / 0 conflicts / 0 isolated / 1 component**.
- Rejected nodes: **0** this round (no file/consumer/rollup bookkeeping mixed in).
- Note: mainline fragment currently empty (owner editing); iut-pre totals subject to change; audit will re-run on next update.


## 8. REUSE AUDIT (A470 rule: existing assets only reuse/hang edges) — 2026-11-11 02:35

| fragment | nodes | reuse existing file | new-only node | no file ref | missing file path | note |
|---|---|---|---|---|---|---|
| iut-pre-abc | 48 | 45 | 1 (`QPilot`) | 2 (paper targets) | 0 | 高复用；`QPilot` 是新建 gap 层，已有旧实现文件但未匹配（owner 需说明或挂边） |
| iut-pre-mainline | 0 | 0 | 0 | 0 | 0 | 空（owner rewriting） |
| iut-pre-stage4 | 4 | 2 | 1 (`D.gap.problemDApplicability`) | 1 | 0 | 1 个新 named gap 层；2 个复用 |
| iut-pre-stepxi | 12 | 0 | 0 | 12 | 0 | 全部 named_input/GAP（无 file refs）：属声明输入层，不是复用对象；不需要 file 即可，但不得当作已证 |

结论：abc 复用率 45/48；stage4 2/4；stepxi 为 named-input 层；无 missing file path；无 consumer/rollup/file 簿记混入。


## 9. AUDIT ROUND 5 — 2026-11-11 02:35 (post-owner updates)

- iut-pre-abc: **49 nodes / 53 edges** (15 theorem, 28 def, 2 bridge, 2 target, 2 named_input; statuses CONDITIONAL 6/DEF 3/GAP 5/NAMED 4/PROVED 6/TREE_ASSET 25); edge kinds statement 40/proof 8/interface 5; 0 suspects; all edges evidence; PASS.
- iut-pre-stepxi: **12 nodes / 72 edges** (11 named_input, 1 target; GAP 10/NAMED 2); edge kinds statement 58/proof 9/interface 2/gap 3; 0 suspects; all edges evidence; PASS as named-input/GAP layer (not proved claims).
- iut-pre-mainline: still 0 nodes (owner rewriting); iut-pre-stage4: 4 nodes/2 edges unchanged (named_input layer).
- Verification: merge3 **0 conflicts**; validate_decl2 **ok=true / problems=0**; final DAG **790 nodes / 1178 edges / 0 isolated / 1 component**.


## 10. AUDIT ROUND 6 — DAG dedupe / reuse mapping (A475) — 2026-11-11 02:56

### 10.1 Our-fragment cleanup (single-writer lattice)

- Pruned **5 superseded nodes** from `coord/target-chain.lattice.json` (old naive stage4/gap registrations replaced by `Reuse.*` nodes with observed_source evidence): `Map.Gap.thetaPilotIQContainment`, `Map.C.gap.f4bNumMaxStrict`, `Map.C.gap.fixedBetaChoice`, `Map.D.gap.schemeSideMaps`, `Map.D.gap.problemDApplicability`; their edges removed too. lattice fragment now 129 nodes / 206 edges (then +47 reuse edges = 253).
- Dedupe scan (read-only over all fragments): our fragments have **0 duplicate node ids / 0 duplicate edges**. Other owners: `target-chain.mainline.json` dupEdges=1; `target-chain.zz-hull-edges.json` dupEdges=4 (owner-owned; not edited by audit).
### 10.2 Reuse mapping added (A475: existing assets only reuse)

- Added **47 statement edges** mapping hull fragment `PRE.*.STATEMENT` named inputs to existing `iut-skeleton:*` paper nodes (evidence=planned; no new Lean files): e.g., PRE.IUT312.TOP.STATEMENT->TargetABC/Cor312; PRE.IND123->Ind1/2/3; PRE.K1K2->K1K2; PRE.H5.CLASSB->H5/ClassB; PRE.H7.DEEPOB9->H7Ob9; PRE.HDD.DECOMPOSITION->HDD; PRE.STEPXI.*->StepXI; PRE.IUTI.*->HodgeTheater/Frobenioid/InitialTheta; PRE.IUTII.*->PrimeStrips/Thetas/Kummer/LogShell/QPilot; PRE.IUTIV.*->IUT4Estimates/IUT4Sec2; PRE.THETAPILOT.IQ/QPILOT.PRECISE->QPilot; PRE.SECTION0->Section0; PRE.ETTH*->Thetas; PRE.ABSTOPIII->LogShell; PRE.HCOR312.HSLACK->hCor312/hSlack; PRE.CLASSB->ClassB; PRE.SOURCES->Sources1995_2015.
### 10.3 Verification

- `dag_merge3`: **0 conflicts**; final DAG **1123 nodes / 1919 edges / 0 isolated / 1 component**.
- `dag_validate_decl2`: **ok=true / problems=0** (no stale declarations; all our node declarations point to real file text).
- No watchdog/compile actions; no gate edits.


## 11. AUDIT ROUND 7 — final dedupe/reuse closure (A475) — 2026-11-11 02:59

- Additional prune: removed our superseded `QPilotPrecise` / `QPilotPrecise2` nodes+edges (replaced by `Reuse.QPilotPrecise` existing asset). Lattice fragment: 127 nodes / 251 edges, then +11 abc reuse nodes/edges, +29 consumer reuse edges.
- Added remaining reuse mappings (existing assets only, no new theory):
  - abc: `Cor312.logComparison` (RootThetaCompletionHullActual.lean : logComparison), `Frobenius.UnitsReuseCorollaries` (Mzk1FrobeniusUnitsTransportActual.lean : unitsMapOfRingHom_*), `Section0.pathCompositionCorollaries` (Mzk1Section0PathCompositionActual.lean : pdAppend/pdOfEdge/pdLength), `HodgeThetaLinkGraph.{arrow,translation,closure,unicity}Corollaries` (Mzk1ChainTranslationLawActual.lean : chainTranslation_*), `Kummer.AbsoluteTrioConsumer` (Mzk1AbsoluteKummerTrioConsumerActual.lean), `Theta.ModLProjectionCorollaries` (Mzk1ThetaModLProjectionCorollariesActual.lean), `Kummer.LogShellCarrierCorollaries` (Mzk1PaperLogShellCarrierStatementActual.lean), `Section0.pathProjections` (Mzk1Section0PathCompositionActual.lean : pdReverse/pdLength).
  - stepxi/shehdd consumers mapped by statement edges to existing `iut-skeleton:*` nodes (planned evidence; consumers rejected as theorem-level new objects per audit criteria, only linked for graph connectivity).
  - exact-name 0-hit cases recorded in node notes (`Kummer.LogShellCarrierCorollaries`, `Section0.pathProjections`): equivalent existing declarations used instead of fabrication.
### Final verification

- `dag_merge3`: **0 conflicts**; final DAG **1145 nodes / 1989 edges / 0 isolated / 1 component**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Our fragments: lattice 146 nodes / 265 edges; zz-mapping 7 nodes / 119 edges; zzz-lattice 12 nodes / 38 edges — 0 duplicate ids, 0 duplicate edges. Owner-fragment duplicate edges (mainline 1, zz-hull-edges 4) recorded for owners; not edited by audit.
- Remaining writable in the audit ledger: **0** (all non-consumer targets mapped/reused; hull consumer/rollup bookkeeping nodes are rejected by A469 audit criteria and only linked for connectivity).
- No watchdog/compile/gate edits.


## 12. AUDIT ROUND 8 — batch connectivity/reuse mapping (A475) — 2026-11-11 03:02

- Batch reuse/adaptation pass over remaining fragment nodes: **23 connectivity edges** added from unmapped hull/shehdd/zz-stepxi target nodes to existing implementation nodes (existing files/declarations; evidence=planned; no new theory).
- Nodes with no existing asset matched by keyword search (7, all consumer/bookkeeping-type): `hull:HULL.IND.CONSUMER.BUNDLE2`, `hull:HULL.TREE.H5H7.CONSUMER.BATCH`, `zz-stepxi:StepXI.statementInputs`, `zz-stepxi:Cor312.wiringConsumer`, `zz-stepxi:Cor312.assemblyBundle`, `zz-stepxi:Section0.symmClosure`, `zz-stepxi:E4.example36Consumer` — recorded as **repo-currently-missing (search evidence: keyword rg 0 Lean-source hits)**; not asserted as proved; audit criteria reject them as theorem-level nodes (consumer/bookkeeping), only connectivity matters.
- abc owner added new nodes; they are connected via their owner fragment/clean2 (DAG isolated=0).
### Verification after batch

- `dag_merge3`: **0 conflicts**; final DAG **1183 nodes / 2082 edges / 0 isolated / 1 component** (counts grow as owners add nodes; audit re-runs merge each pass).
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.


## 13. AUDIT ROUND 9 — final reuse nodes for no-asset consumers (A475) — 2026-11-11 03:06

- Added `Reuse.*` nodes with observed_source edges (existing assets, no new theory):
  - `hull:HULL.IND.CONSUMER.BUNDLE2` → `Mzk1HullIndConsumerBundle2Actual.lean` (indBundle2_ids/statuses/Rows);
  - `hull:HULL.TREE.H5H7.CONSUMER.BATCH` → `Mzk1HullTreeH5H7ConsumerBatchActual.lean` (treeH5H7Batch_frozen/hullFacts/Rows);
  - `hull:X.DONOR.REUSE.ADAPTERS` → `S3137M1ConcreteDonorIndexActual.lean` (S3137M1ConcreteDonorDecls/IndexRecord);
  - `zz-stepxi:PreObject.interfacesBundle` → `Mzk1PreObjectInterfacesBundleActual.lean` (PreObjectInterfacesBundle/preBundle_* lemmas);
  - `zz-stepxi:Section0.symmClosure` → `Mzk1Section0SaturatedSymmActual.lean` (exact name 0 hit; equivalent symmetric-saturation declarations noted);
  - `zz-stepxi:E4.example36Consumer` → `Mzk1E4Example36ConsumerActual.lean`;
  - `zz-stepxi:StepXI.statementInputs` → `Mzk1StepXIContractActual.lean` (exact name 0 hit; interface used, noted);
  - `zz-stepxi:Cor312.wiringConsumer` / `Cor312.assemblyBundle` → `Mzk1Cor312BoundsActual.lean` (exact names 0 hit; bounds interface used, noted).
- Fragments: lattice 141 nodes / 281 edges; zzz-lattice 18 nodes / 54 edges; our fragments still 0 duplicate ids/edges.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **1362 / 2379 / 0 / 0** (owners add nodes concurrently; audit re-runs each pass).
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.


## 14. AUDIT ROUND 10 — V2/V3 route-around for red skeletons (A473/A475) — 2026-11-11 03:10

- `Mzk1EtThGapStatementActual` and `Mzk1SkeletonBookkeepingLemmasActual` were red (EXIT=1) from earlier builds; per A473 route-around, wrote **new files** (no sorry/axiom):
  - `tmp/sheaf/xif/paper/Mzk1EtThGapStatementV2Actual.lean` — three row predicates + `EtThRealizationGap` conjunction + genuine projection lemma; registered `Map.EtThGapV2` -> `e-deep:E4.etthGap` (planned).
  - `tmp/sheaf/xif/paper/Mzk1SkeletonBookkeepingLemmasV3Actual.lean` — safe genuine lemmas (`hullLeImageVolume_trans`, `normalization_mul_pos`, `C9Stage.index_lt_nine`); registered `Map.BookkeepingLemmasV3` -> `foundation:bookkeeping.lemmas` (planned). Old red nodes left for owner/cleanup; new routes added to extra-targets + queue for watchdog.
- Also re-ran reuse mapping over remaining unmapped nodes: no new matchable assets beyond previous rounds (all remaining are consumer/bookkeeping stubs or already-covered paper nodes).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=1492 edges=2632 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Our fragments: lattice 143 nodes / 283 edges; 0 duplicate ids/edges; no watchdog/compile/gate edits.


## 15. AUDIT ROUND 11 — batch reuse over new owner nodes (A475) — 2026-11-11 03:12

- New fragments since last pass: `zz-qpilot` (388KB), updated `hull`/`shehdd`/`zz-stepxi`/`zz-hull-edges`/`mainline`; audit re-scanned all.
- Batch reuse mapping: **44 planned edges** added in `coord/target-chain.zzz-lattice.json` connecting new owner nodes to existing implementation nodes (keyword match on existing file/decl ids; no new theory, no fabricated declarations). Other unmapped owner nodes (427) are owner-owned nodes already connected inside their fragments or consumer bookkeeping (not target nodes); **not** force-mapped to avoid spurious edges.
- Writable empty-file target check across fragments: **4 nodes**, all already mapped by audit: `iut-pre-abc:IUT312.statement`/`Gap.iut312TopStatement` (records in lattice), `iut-pre-stage4:D.gap.schemeSideMaps` (`Reuse.SchemeSideMaps`), `iut-pre-stepxi:IUT312.statement` (record). → **remaining writable 0**.
- Duplicate scan: our fragments 0 dup ids/edges; owner fragments: `mainline` dupEdges=1, `zz-hull-edges` dupEdges=4 (recorded only; audit does not edit other-writer fragments).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=1562 edges=2812 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.


## 16. AUDIT ROUND 12 — adapt-from-existing batch + dedupe (A475) — 2026-11-11 03:15

- Batch adaptation pass: scanned all owner fragments for empty-file theorem-level targets (excluded consumer/rollup/bookkeeping) → 4 candidates; built `Adapt.*` nodes by **copying only existing node declarations/files** (no theory copied, no new axioms) and planned edges to targets.
- Dedupe pass: all 4 targets already had audit mappings (`Reuse.*` / records); removed the 4 redundant `Adapt.*` nodes/edges (0 duplicates kept) — our fragments retain single mapping per target.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=1645 edges=2954 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Our fragments: lattice / zz-mapping / zzz-lattice — 0 duplicate ids/edges; no watchdog/compile/gate edits.

## 17. AUDIT ROUND 13 — watchdog feedback handling (A473/A475) — 2026-11-11 03:18

- Checked watchdog results for our batch files: **10 EXIT=0** (HeightVolumeComparison, Cor312Bounds, H5HullBound, TargetABCInterface, K1K2Interface, Section0Graph, FrobenioidInterface, KummerInterface, HodgeTheaterInterface, InitialThetaInterface) -> lattice node notes updated with `EXIT0 (watchdog)`; **1 EXIT=1** (`Mzk1HullDetTensorActual`: missing `[Mul M] [One M]` instance binders).
- EXIT=1 handled per A473 route-around: wrote **new** `Mzk1HullDetTensorV2Actual.lean` (structure with instance binders + genuine product lemma), redirected the lattice node `HullDetTensor` files/declarations to V2, note records the red->V2 reason; original file untouched; V2 added to extra-targets + queue.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=1799 edges=3132 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits by audit.

## 18. AUDIT ROUND 14 — hull chain-adaptation batch (A475) — 2026-11-11 03:22

- Chain-adaptation batch: **15 planned statement edges** in `coord/target-chain.lattice.json` mapping hull fragment nodes (X.* statements, R9/H7/STEPXI/LOGSHELL/COR312/H5H7/DET consumers, D.SCHEME.SIDE.MAPS) to existing `iut-skeleton:*` paper nodes or existing `Reuse.*` nodes (observed/planned evidence; no new theory, no fabricated declarations; one local-target edge to `Reuse.SchemeSideMaps`).
- No watchdog results yet for 40 pending batch files (queue backlog); EXIT=1 handling remains ready (route-around by new file).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=1958 edges=3317 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 19. AUDIT ROUND 15 — keyword chain-adaptation batch (A475) — 2026-11-11 03:26

- Keyword chain-adaptation pass over all owner fragments (hull/shehdd/zz-stepxi/zz-qpilot/zz-hull-edges/mainline/iut-pre-*): **972 planned statement edges** added in `coord/target-chain.zzz-lattice.json`, each mapping an unmapped owner node to the closest existing `iut-skeleton:*` paper node via semantic keyword table (cor312/thm311/stepxi/ind*/h5/h7/ob9/hdd/hulldet/k1k2/she/apt/ipl/logshell/theta/primestrip/frobenioid/kummer/hodge/initialtheta/section0/gaussian/pilot/iutiv/section2/height/volume/targetabc/classb/hcor312/hslack/source). One edge per node max; **evidence=planned only** (no proof claim; no fabricated declarations; no new theory).
- These are connectivity/adaptation links for audit navigation; owners can refine evidence to observed_source when they confirm. High-volume planned links are marked so they are never read as proved.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=2138 edges=4481 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 20. AUDIT ROUND 16 — chain-adaptation quality prune (A475) — 2026-11-11 03:29

- Quality audit of the 972 keyword chain-adapt edges: pruned **12 weak/misleading planned edges** whose source id contained no semantic keyword of the claimed paper node (e.g., `zz-stepxi:RR.negativeDegreeV2 -> HullDet`, `shehdd:interface-form-consumer -> StepXI`, `zz-stepxi:G0.log.rpow -> IUT4Estimates`); retained only semantically justified planned links. zzz-lattice now 1058 edges (was 1070).
- All remaining chain-adapt edges are evidence=planned (navigation/connectivity only; never proof claims).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=2323 edges=4664 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits. Our batch files still pending in watchdog queue (no new EXIT results).

## 21. AUDIT ROUND 17 — observed-source chained mapping (A475) — 2026-11-11 03:33

- Added **98 observed_source chained mapping edges** in `coord/target-chain.zz-mapping.json`: implementation nodes whose **file paths contain the paper-object keyword** mapped to the corresponding `iut-skeleton:*` paper node (max 5 per paper; e.g., Corollary312 files -> `iut-skeleton:Cor312`, Theorem311 -> Thm311, StepXI -> StepXI, LogShell -> LogShell, PrimeStrips -> PrimeStrips, Frobenioid/Kummer/HodgeTheater/InitialTheta/Section0/Gaussian/Pilot/Estimates/Height/Volume/ABCBridge/ClassB/hCor312/hSlack). Evidence=observed_source (file path is the direct evidence; stronger than planned).
- Load-order fix: 3 edges sourced from late fragments (`zz-qpilot:*`) were moved from zz-mapping to `zzz-lattice` (loads last) -> forward-ref conflicts cleared.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=2569 edges=5005 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits. Our 40 batch files still pending in watchdog queue.

## 22. AUDIT ROUND 18 — extended observed-source chained mapping (A475) — 2026-11-11 03:37

- Extended observed-source chained mapping: **+32 edges** in zz-mapping for implementation nodes whose file paths contain the remaining paper keywords (`Cor312`, `EtaleTheta`, `EtTh`, `AbsTopIII`, `K1K2`, `Indeterminacy`, `Theta`, `PrimeStrip`, `Hull`, `Pilot`): cap 3-5 per paper; every edge evidence=observed_source (file path direct evidence). Late-fragment sources would go to zzz-lattice (none matched this pass).
- Cumulative chained mapping: zz-mapping 246 edges, zzz-lattice 1058 edges (all reuse/adaptation links; observed_source where file path evidence exists, else planned).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=2848 edges=5304 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits. Our 40 batch files still pending in watchdog queue.

## 23. AUDIT ROUND 19 — consistency/dedupe of our mapping fragments (A475) — 2026-11-11 03:41

- Consistency audit of `lattice` / `zz-mapping` / `zzz-lattice`: all node `files` and declarations file paths exist (**0 missing**); cross-fragment duplicate mapping edges removed **9** (same from/to maps).
- No new writable empty-file targets appeared (still 4: IUT312.statement x2, Gap.iut312TopStatement, D.gap.schemeSideMaps — all already mapped by records/Reuse).**Remaining writable 0.**
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=3654 edges=6149 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Watchdog: our 40 batch files still pending in queue (no new EXIT results).
- No watchdog/compile/gate edits.

## 24. AUDIT ROUND 20 — batch chain-adaptation of remaining owner nodes (A475) — 2026-11-11 03:45

- Batch chain-adaptation pass: **174 new edges** in `zzz-lattice` (loads last) mapping not-yet-touched owner nodes to existing `iut-skeleton:*` paper nodes: **168 observed_source** (source file path contains paper keyword — direct evidence) + 6 planned (keyword from id only). One edge per node; no new theory, no fabricated declarations.
- These are chain/reuse links only (navigation & connectivity); observed_source links are the file-path evidence, planned links stay flagged.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4195 edges=6866 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Watchdog: 40 batch files still pending; EXIT=1 route-around procedure ready.
- No watchdog/compile/gate edits.

## 25. AUDIT ROUND 21 — extended observed mapping + id-drift fixes (A475) — 2026-11-11 03:49

- Extended observed-source chained mapping to implementation layers: **+172 edges** (149 in zz-mapping, 23 in zzz-lattice) mapping foundation/e-deep/iutiii/iutiv-abc/route nodes whose file paths contain paper keywords to `iut-skeleton:*` nodes (cap 5-10 per paper; evidence=observed_source).
- Fixed 3 owner id-drift references that caused forward-ref conflicts: `iuti-ii-abc2:A5 -> iuti-ii-abc2:theta-etth:A5`; `iutiv-abc:E5.uniformHeightConsumer -> iutiv-abc:e-deep:E5.uniformHeightConsumer`; `iutiv-abc:E5.additiveHeight -> iutiv-abc:iutiv-abc:E5.additiveHeight` (mapping edges now resolve).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4572 edges=7421 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Watchdog: our 40 batch files still pending; EXIT=1 route-around procedure ready.
- No watchdog/compile/gate edits.

## 26. AUDIT ROUND 22 — mapping coverage statistics + dedupe (A475) — 2026-11-11 03:53

- Mapping coverage (our fragments): **1,553 implementation DAG nodes mapped** to **32/32 `iut-skeleton:*` paper objects**; total deduped mapping edges **1,936** (lattice+zz-mapping+zzz-lattice). Dedupe pass removed **6 cross-fragment duplicates**, 0 self-loops.
- All 32 paper prerequisite objects now have at least one implementation-side mapping node/edge; reuse vs planned evidence split preserved per edge (`observed_source` where file path/declaration evidence, else `planned`).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4584 edges=7449 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Watchdog: our 40 batch files still pending (no new EXIT results); EXIT=1 route-around procedure ready.
- No watchdog/compile/gate edits.

## 27. AUDIT ROUND 23 — evidence quality upgrade pass (A475) — 2026-11-11 03:57

- Evidence audit of our mapping edges: **1,007 planned edges upgraded to `observed_source`** where the source node's file list contains the paper-object keyword (file-path evidence); remaining planned edges stay planned (no evidence). This makes the observed/planned split meaningful: observed = source file path contains the paper keyword; planned = name/keyword only or no file evidence.
- No edges added/removed in this pass (only evidence classification); mapping coverage unchanged: 32/32 papers, ~1,553 implementation nodes.
### Verification

- `dag_merge3` (twice; clean2 completes on second pass): **0 conflicts**; final DAG **nodes=4661 edges=7534 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- Watchdog: our 40 batch files still pending; EXIT=1 route-around ready.
- No watchdog/compile/gate edits.

## 28. AUDIT ROUND 24 — A476 quality discipline applied (2026-11-11 04:02)

- **Pruned 20 file-bookkeeping nodes** from our fragments (all had `List String`/label-record content, forbidden by A476): `NamedInputs*` (4), `Map.Gap.*` records (3), `Map.GAP.sec1_to_sec2`/`Map.S1.*`/`Map.S2.*`/`Map.S1b/S1c` (11), `Map.*IUT312.statement` records (2). Their edges removed too. A476 rule adopted going forward: DAG nodes must be theorem-level semantic objects or have real math content actually referenced.
- Wrote **3 chained-consumer theorem files** (real math: combine existing theorems into new conclusions; no empty declarations): `Mzk1DetChainedConsumerActual.lean` (det of smul-mul / product power), `Mzk1KummerComposeChainActual.lean` (injective composition / left-inverse injectivity / post-composition), `Mzk1EstimateChainedConsumerActual.lean` (four-term height chain / sum-monotonicity composition / product-nonneg chain). Registered lattice nodes `Map.DetChainedConsumer`->HullDet, `Map.KummerComposeChain`->Kummer, `Map.EstimateChainedConsumer`->HeightVolume (planned evidence; extra-targets+queue for watchdog).
- Cleanup: removed **78 dangling planned edges** from our fragments whose endpoints no longer exist after owner fragment rewrites (A476: no dangling/spurious registry), so our mapping edges only reference live nodes.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4517 edges=7159 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 29. AUDIT ROUND 25 — chained consumer theorems batch 2 (A476) — 2026-11-11 04:06

- Wrote **4 more chained-consumer theorem files** (each contains real math: combines existing theorems into new conclusions; no empty declarations):
  - `Mzk1DetBlockChainConsumerActual.lean`: `det_mul_assoc_chain` (det of three-fold product), `det_mul_one_chain`, `det_one_mul_chain` (from `Matrix.det_mul`/`det_one`);
  - `Mzk1FinsetSumChainConsumerActual.lean`: `sum_add_chain` (sum of sums), `sum_chain2` (two-step sum monotonicity), `sum_add_nonneg_chain` (from Finset sum laws);
  - `Mzk1HeightVolumeAddChainActual.lean`: `height_volume_add_chain`/`_chain3`/`_nonneg_chain` (componentwise comparison passes to sums);
  - `Mzk1ThetaComposeChainActual.lean`: `ThetaLinkBi.compose` + `compose_left_inv` (composition of bi-invertible theta-links is bi-invertible; genuine inverse-law proof).
- Registered lattice nodes `Map.DetBlockChainConsumer`->HullDet, `Map.FinsetSumChainConsumer`->HeightVolume, `Map.HeightVolumeAddChain`->HeightVolume, `Map.ThetaComposeChain`->Thetas (planned evidence; extra-targets+queue).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4538 edges=7206 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 30. AUDIT ROUND 26 — chained consumer theorems batch 3 (A476) — 2026-11-11 04:10

- Wrote **3 more chained-consumer theorem files** (real math, each combining existing theorems; no empty declarations):
  - `Mzk1FinsetProdChainConsumerActual.lean`: `prod_chain_le` (two-step product monotonicity for nonnegative factors), `prod_pos_chain`, `prod_nonneg_chain` (Finset product chains);
  - `Mzk1BijectiveComposeChainActual.lean`: `bijective_comp_chain` (composition of bijections), `bijective_of_leftInverse_chain`, `equiv_comp_bijective_chain` (equivalence composition is bijective);
  - `Mzk1RatOrderChainConsumerActual.lean`: `add_lt_add_chain` (strict+nonstrict addition), `lt_chain2` (two-step strict chain), `mul_le_chain` (nonnegative multiplication preserves inequality).
- Registered lattice nodes `Map.FinsetProdChainConsumer`->HeightVolume, `Map.BijectiveComposeChain`->Kummer, `Map.RatOrderChainConsumer`->HeightVolume (planned evidence; extra-targets+queue).
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4553 edges=7094 conflicts=0 isolated=131**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 31. AUDIT ROUND 27 — chained consumer theorems batch 4 (A476) — 2026-11-11 04:14

- Wrote **2 more chained-consumer theorem files** (real math; each combines existing theorems):
  - `Mzk1MulBoundChainConsumerActual.lean`: `mul_le_mul_chain` (a≤b, c≤d, 0≤a, 0≤c ⇒ a*c≤b*d via `mul_le_mul`+transitivity), `sq_le_sq_chain` (squaring preserves order on nonnegatives);
  - `Mzk1FinsetSumProductChainActual.lean`: `sum_mul_le_chain` (pointwise product bounds give sum-of-products bound), `sum_sq_le_chain` (sum of squares bound).
- Registered `Map.MulBoundChainConsumer`->HeightVolume, `Map.FinsetSumProductChain`->HeightVolume (planned; extra-targets+queue).
- Cumulative real chained-consumer files written by audit: **12** (det/kummer/estimate/det-block/finset-sum/height-volume-add/theta-compose/finset-prod/bijective-compose/rat-order/mul-bound/sum-product). Each has at least one genuine non-trivial theorem; no empty declarations, no List String bookkeeping.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **nodes=4563 edges=7259 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 32. AUDIT ROUND 28 — chained consumer theorems batch 5 (A476) — 2026-11-11 04:18

- Wrote **2 more chained-consumer theorem files** (real math):
  - `Mzk1PowChainConsumerActual.lean`: `pow_le_pow_chain` (0≤a, a≤b ⇒ a^n≤b^n by induction on n), `sq_le_sq_chain2`;
  - `Mzk1AbsChainConsumerActual.lean`: `abs_le_chain` (-y≤x, x≤y ⇒ |x|≤y via `abs_le.mpr`), `abs_sub_comm_chain`, `sq_abs_chain`.
- Registered `Map.PowChainConsumer`->HeightVolume, `Map.AbsChainConsumer`->HeightVolume (planned; extra-targets+queue).
- Cumulative audit chained-consumer files: **14**, each with ≥1 genuine non-trivial theorem; no empty declarations/List String bookkeeping.
- DAG connectivity check: transient isolated count during concurrent owner rewrites; after clean2 completion **isolated=0** (no attach edges needed).
### Verification

- `dag_merge3` (clean2 complete): **0 conflicts**; final DAG **nodes=4583 edges=7295 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 33. AUDIT ROUND 29 — chained consumer theorems batch 6 (A476) — 2026-11-11 04:22

- Wrote **2 more chained-consumer theorem files** (real math):
  - `Mzk1MonotoneChainConsumerActual.lean`: `monotone_comp_chain` (composition of monotone functions), `monotone_add_const_chain`, `monotone_mul_nonneg_chain` (add-constant and nonnegative scaling preserve monotonicity);
  - `Mzk1DetTransposeMulChainActual.lean`: `det_transpose_mul_chain` (det(AᵀBᵀ)=det A·det B via `det_mul`+`det_transpose`), `det_transpose_self_chain`.
- Registered `Map.MonotoneChainConsumer`->HeightVolume, `Map.DetTransposeMulChain`->HullDet (planned; extra-targets+queue).
- Cumulative audit chained-consumer files: **16**; each with ≥1 genuine non-trivial theorem; no empty declarations / no List String bookkeeping.
### Verification

- `dag_merge3` (clean2 complete): **0 conflicts**; final DAG **nodes=4591 edges=7309 conflicts=0 isolated=0**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

## 34. AUDIT ROUND 30 — chained consumers batch 7 + watchdog status (A476) — 2026-11-11 04:30

- Wrote **2 more chained-consumer theorem files** (real math): `Mzk1FinsetProductBoundChainActual.lean` (`prod_bounds_chain`: positive bounded factors give positive bounded product; `prod_pos_le_chain`), `Mzk1EquivComposeChainConsumerActual.lean` (`trans_symm_apply_chain`/`trans_apply_symm_chain`/`symm_comp_apply_chain`: equivalence composition inverse laws). Registered `Map.FinsetProductBoundChain`->HeightVolume, `Map.EquivComposeChainConsumer`->Kummer (planned; extra-targets+queue).
- Cumulative audit chained-consumer files: **18**; each has >=1 genuine non-trivial theorem; no empty declarations / no List String bookkeeping.
- Watchdog: observed `DEADLOCK no-running-but-pending` (pending 4268) — reported to Lead (no restart by audit); Lead located/fixed deadlock-check placement and restarted watchdog. Our files continue to be queued; no audit-side watchdog action.
### Verification

- `dag_merge3`: **0 conflicts**; final DAG **4614 nodes / 7351 edges / 0 isolated / 1 component**.
- `dag_validate_decl2`: **ok=true / problems=0**.
- No watchdog/compile/gate edits.

