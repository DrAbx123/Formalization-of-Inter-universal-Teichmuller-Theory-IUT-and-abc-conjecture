# DAG build report (final, machine-checked)

## Layer A — file import graph
| metric | value |
|---|---|
| nodes (all .lean files) | 123,411 |
| edges (root-aware imports) | 36,618 |
| import cycles (SCC) | 0 |
| external import names (Mathlib etc.) | 75,664 |
| files with olean present | 8,765 |
| files with last watchdog EXIT=0 | 4,012 |
| files with last watchdog EXIT!=0 | 561 |
| files containing `sorry` token (mechanical) | 2,354 |
| files containing `axiom`/`constant` declaration (mechanical) | 1,066 |
| validator | **ok=true** (dag/DAG-VALIDATION.json) |

Note: the only genuine import cycle found earlier (`S3139FieldCCopyActionActual` <-> `S3139FieldCArchimedeanRealActual`) was fixed by mainline (direct imports) before this run; cyclic components = 0.

## Layer B — declaration-level route DAG
| metric | value |
|---|---|
| nodes | 63,606 |
| edges | 1,498 |
| fragment merge conflicts | 0 |
| proof+interface subgraph | acyclic (all 716 reached) |
| statement/citation subgraph | cyclic (paper citation graph; informational) |
| validator problems | 0 |
| validator | **ok=true** (dag/DECLARATION-DAG-VALIDATION.json) |

Online routes: 12 external route candidates (LANA project/interim report; IUT Validation; Bridge Certificate with 4 applications; IUT Comes Home; Joshi FAQ; Scholze-Stix report; Hayashi impossibility; Mochizuki Formalization report; LeanForm ZFC; autoformalization; IUAni animations), status=EXTERNAL, evidence-only (no proof claims). Complete-universe additions: route-mentions fragment (42,770 nodes from 9,515 docs) + paper-labels fragment (20,091 nodes from 257 papers); no edges (evidence indexes attached to the route DAG).

Fragments: main 26/21; foundation 21/17; e-deep 23/17; iuti-ii 31/37; iutiii 29/23; iutiv-abc 36/52; legacy-dag 89/147; paper-routes 46/76; paper-theta 383/1082; theta-etth 32/26.

## Layer C — declaration universe
| metric | value |
|---|---|
| declarations indexed | 1,572,263 |
| files covered | 123,410 |
| index size | ~273 MB (dag/generated/declarations-index.json) |

## Coverage evidence (where the routes came from)
- Paper corpus: 257 text files (14.1MB) — IUT I-IV, Explicit estimates, Essential Logical Structure, Alien Copies, Hodge-Arakelov surveys, AbsTopIII, EtTh, GenEll, NCBel, Frobenioid I-II, Combinatorial Anabelian I-IV, FAQ, IUT Program, Formalization of IUT (2026-04).
- `coord/PAPER-INDEX.json` (auto: sections/theorem-like labels), `coord/PAPER-ROUTES.md` (per-paper route map), `coord/ROUTE-MENTIONS.md` (10 route families R1-R10 incl. archived/refuted/obstruction), `coord/REPO-ROUTE-INDEX.md` (897 route-like files, 671 uncovered by old docs, per-owner triage TSV).
- Legacy SHEAF DAG: 89 nodes (`dag/nodes/*.json`) converted into legacy-dag fragment.
- Official route layer: Mochizuki 'Formalization of IUT (2026-04)' Stage 1-5 + §4 four-triangle species/mutation structure, mapped to repo files `IUTIII/Corollary312/{Routes,Comparison,Obligations}` and `StepXI/{Contract,IPL,SHE,APT}`.

## Honest caveats
- PROVED/BOTTOM only for nodes whose files/declarations were verified; CONDITIONAL/NAMED/GAP are explicit.
- `sorry`/`axiom` counts are mechanical text counts over all files (many are ported/historical); gate-level axiom discipline is checked separately by probes on cited files.
- Layer B is curated: it is complete w.r.t. the fragments delivered by the team, not yet w.r.t. every declaration in Layer C.