# TARGET-CHAIN JSON MERGE (Lead A436/A437) — process for section fragments -> dag/target-chain.json

**Goal:** curated declaration-level target chain for the IUT -> ABC DAG. Each section submits `coord/target-chain.<section>.json`; **mainline merges** into `dag/target-chain.json`. No proofs; no gate edit; refs only.

**Current base:** `dag/target-chain.json` (14540B; generated_by Lead A436; schema: nodes[] + edges[]; node = {id, kind, title, status, files[], declarations{file:[decls]}}; edge = {from,to,kind: proof|interface|gap}).

## 1. SECTION FRAGMENTS (expected submissions)

| section id | owner | fragment path | status |
|---|---|---|---|
| iuti-ii | abc | coord/target-chain.iuti-ii.json | LANDED (32691B; 31 nodes/37 edges; abc routes to be added) |
| iutiv-abc | stepxi | coord/target-chain.iutiv-abc.json | LANDED (22516B; 31 nodes/42 edges) |
| iutiii | hull | coord/target-chain.iutiii.json | LANDED (18444B; 29 nodes/23 edges; S11 skeleton still ETA) |
| theta-etth | qpilot | coord/target-chain.theta-etth.json | LANDED (49026B; S12 skeleton landed) |
| paper-routes | hull | coord/target-chain.paper-routes.json | EXPECTED (A439; prefix paper:; Stage 1-5 + §4 species/mutation; statuses GAP/NAMED allowed; merge LAST) |
| foundation | lattice | coord/target-chain.foundation.json | PENDING (mainline adds) |
| e-deep | mainline/lattice | coord/target-chain.e-deep.json | PENDING (mainline adds) |

## 2. TEMPLATE + VALIDATION

- Template: `coord/target-chain.TEMPLATE.json` (fields: meta.section/author/date; nodes[]; edges[]).
- Required per node: unique id (prefix with section), kind, title, status in {DEF, PROVED, CONDITIONAL, NAMED, TREE_ASSET}, files[] existing paths (or tree paths marked), declarations{} keys equal to files (decl names must appear in those files).
- Required per edge: from/to ids exist in base+new nodes; kind in {proof, interface, gap}.
- Validation snippets: JSON parse (`Get-Content -Raw | ConvertFrom-Json`); duplicate id check; edge endpoint check; file existence check; declaration name grep in file; status whitelist. Reject on any error; report offender.
- Honesty: every node claims only what its files prove; named/conditional nodes marked; no new proof claim from JSON.

## 2b. ACTUAL MERGE MECHANISM (A438/A439; tools/dag_merge2.mjs)
- **Sources:** `dag/target-chain.json` (main base, no prefix) + every `coord/target-chain.<section>.json` in coord; **`target-chain.TEMPLATE.json` is EXCLUDED** by regex (`^target-chain\..+\.json# TARGET-CHAIN JSON MERGE (Lead A436/A437) — process for section fragments -> dag/target-chain.json

**Goal:** curated declaration-level target chain for the IUT -> ABC DAG. Each section submits `coord/target-chain.<section>.json`; **mainline merges** into `dag/target-chain.json`. No proofs; no gate edit; refs only.

**Current base:** `dag/target-chain.json` (14540B; generated_by Lead A436; schema: nodes[] + edges[]; node = {id, kind, title, status, files[], declarations{file:[decls]}}; edge = {from,to,kind: proof|interface|gap}).

## 1. SECTION FRAGMENTS (expected submissions)

| section id | owner | fragment path | status |
|---|---|---|---|
| iuti2 | abc | coord/target-chain.iuti2.json | pending |
| iutiv-abcbridge | stepxi | coord/target-chain.iutiv-abcbridge.json | pending |
| iutiii-hull | hull | coord/target-chain.iutiii-hull.json | pending (S11 skeleton also ETA) |
| theta-etth | qpilot | coord/target-chain.theta-etth.json | pending (S12 skeleton landed) |
| foundation | lattice | coord/target-chain.foundation.json | pending |
| e-deep | mainline/lattice | coord/target-chain.e-deep.json | pending |

## 2. TEMPLATE + VALIDATION

- Template: `coord/target-chain.TEMPLATE.json` (fields: meta.section/author/date; nodes[]; edges[]).
- Required per node: unique id (prefix with section), kind, title, status in {DEF, PROVED, CONDITIONAL, NAMED, TREE_ASSET}, files[] existing paths (or tree paths marked), declarations{} keys equal to files (decl names must appear in those files).
- Required per edge: from/to ids exist in base+new nodes; kind in {proof, interface, gap}.
- Validation snippets: JSON parse (`Get-Content -Raw | ConvertFrom-Json`); duplicate id check; edge endpoint check; file existence check; declaration name grep in file; status whitelist. Reject on any error; report offender.
- Honesty: every node claims only what its files prove; named/conditional nodes marked; no new proof claim from JSON.

 minus template).
- **Prefix = filename key:** section = filename between `target-chain.` and `.json`; merged node ids = `<section>:<id>` (main base keeps raw ids, prefix "").
- **Node conflict:** duplicate namespaced id => conflict recorded, later duplicate skipped (first wins; main base loaded first).
- **Edge handling:** fragment edges must have both endpoints inside the SAME fragment (idmap); otherwise conflict recorded. Edges deduped by `from|to|kind`; kind must be proof|interface|gap (schema).
- **Output:** `dag/declaration-dag.json` = {generated_by, merged_from[source,nodes,edges,prefix], node_count, edge_count, conflicts[], nodes[], edges[]}; conflicts list + console summary.
- **Rerun:** `node tools/dag_merge2.mjs` (from repo root).
- **New source A439:** `coord/target-chain.paper-routes.json` (hull product; id prefix `paper:`; official Stage 1-5 + §4 four-triangle species/mutation diagram). **NOT YET DELIVERED** (file missing at 00:18). **Desired merge order:** main base -> section fragments -> paper-routes (paper last). **Status note:** paper nodes may be `GAP`/`NAMED` (not formalized) — do NOT conflate with PROVED. Current tool discovers fragments via readdir order; because paper ids are namespaced (`paper:`) conflicts are unlikely; if strict last order is required, rename to `target-chain.zz-paper-routes.json` or add explicit order in the tool (mainline owns tool).
- **Current merge (A439/A440):** **154 nodes / 159 edges / 0 conflicts**; sources: main 26/21; iuti-ii 31/37; iutiii 29/23; iutiv-abc 36/52; theta-etth 32/26; paper* pending. Output dag/declaration-dag.json updated.
- **A438 graph rebuild:** import cycle S3139 FIXED (direct imports replace umbrella import; CopyAction EXIT0 7247B); dag/generated rebuilt 123410/36617; validator ok=true (cyclic 0) => dag/generated re-ingest allowed; paper* rename/re-sort allowed. No gate edit.

## 2c. MERGE TOOL v3 + CONTINUOUS MODE (Lead A448 workflow)
- **`tools/dag_merge3.mjs`** = current merge tool: sources `dag/target-chain.json` + `coord/target-chain.<section>.json` (TEMPLATE excluded); prefix = filename key; **cross-fragment edges allowed** (edge endpoints resolved against fragment idmap OR already-merged ids); dedupe by from|to|kind; output `dag/declaration-dag.json` with `merged_from` stats {source,nodes,edges,prefix}, `node_count`, `edge_count`, `conflicts`.
- **`tools/dag_next.mjs`** = actionable-node extractor -> `coord/DAG-NEXT.md` (excludes `coord/DAG-BLOCKED.json` blocked/refuted/detoured); prints actionable/blocked/ready counts.
- **Continuous loop:** dag_next -> pick node with fewest unproved deps in own area -> write Lean + register node/edges in own `coord/target-chain.<section>.json` -> add new file to `dag/watchdog/extra-targets.txt` (or queue head; do NOT start old queue runner) -> watchdog compiles (topo order, max 12 lean) -> run `tools/xif_citable_check.ps1` -> green: set fragment node status PROVED + report pin; red: keep CONDITIONAL + reason; refuted/chain-broken: add to `coord/DAG-BLOCKED.json` and move on.
- **Counts (latest A467/A468):** formal DAG 701 nodes / 976 edges / 0 conflicts / isolated 0 (merge3 auto-runs clean2: schema self-heal + real import wiring + connectivity; do NOT hand-write declaration-dag.json). A465 isolated 93->0; A467 paper<->implementation mapping: `coord/target-chain.zz-mapping.json` 108 edges (58 observed_source / 50 planned), no nodes, loaded last; routes fragment internal statement/proof edges.

## 3. MERGE STEPS (mainline)

1. Collect fragments from section owners; validate each against §2.
2. Merge into `dag/target-chain.json`: append new nodes (dedupe by id; conflicts -> latest verified wins, record correction), append edges (dedupe), update meta.generated_by/date and meta.sections list.
3. Re-validate merged JSON (parse + id uniqueness + edge endpoints); run any DAG checker available; report counts (nodes/edges, per-section).
4. Record event in AUDIT_LEDGER/STATE; no gate edit; pins sidecar canonical remains V150@18248/CFC6CE08.
5. Sections keep own fragments as source; mainline merged file is the DAG input.

## 4. STATUS

- A438: merge mechanism live (tools/dag_merge2.mjs); merged output dag/declaration-dag.json.
- A439: paper-routes source registered (prefix paper:; EXPECTED; merge last; GAP/NAMED only). Merge: 154 nodes / 159 edges / 0 conflicts.
- A440: multi-file `target-chain.paper*.json` rule (each own prefix; all paper last; lexicographic); graph rebuild A438 (123410/36617, validator ok, cyclic 0) allows re-ingest/re-sort. Maintain counts on each new fragment.
- No gate edit; GATE NOT PASSED; binding HOLD; L8 FROZEN; registry 14041 / record 18800.

