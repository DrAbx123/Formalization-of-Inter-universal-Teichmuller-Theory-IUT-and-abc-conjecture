# SORRYAX / recent compile audit — 2026-11-08 02:00

Scope: recompiled/scanned recent `tmp/sheaf/xif/paper` files and their `.out` logs.

## CONFIRMED sorryAx (must not be cited as ACTUAL)

| file | evidence | status |
|---|---|---|
| S3074PhiFixesKActual | RESTORED: fresh EXIT=0, olean 37752 B SHA FBA7B6B4..., `#print axioms` trio, no sorryAx; old `.out` superseded | **ACTUAL/citable** |
| S3075PhiFixesKActual | `.out` says `S3075_phi_fixes_K` depends on `sorryAx`; source currently absent | **INVALID/待修** |
| S3078PhiFixesGenerator | `.out` says `S3078_phi_fixes_generator` depends on `sorryAx`; source currently absent | **INVALID/待修** |
| S3035OrderTwoAlgebraClassification | source lines 94/97 contain `sorry`; no olean | **INVALID** |
| S2906CorrectedDownstreamAudit | `.out` contains `sorryAx`; fresh recompile EXIT=1 (missing Category instance line 39); no olean | **not citable** |
| S2930PerTripleThetaLeRegionActual | `.out` contains `sorryAx`; fresh recompile EXIT=1 (ring/unsolved goals); no olean | **not citable** |
| older S2859* / S2811P* / S268x etc. | `.out` logs contain sorryAx (Nov 6-7) | **historical, not citable** |

## Recompiled ACTUAL in this pass

- S3068OpenImmersionFactorizationActual EXIT=0.
- S3069RangeInclusionActual EXIT=0.
- S3070HnonActual EXIT=0.
- S3071BranchFactorExtraction EXIT=0.
- S3078QPrimePseudofunctorTarget EXIT=0 (coherence target; mapComp still missing).
- S3104ClausesCtoF EXIT=0.
- S3107MultiPrimeAuditActual EXIT=0.
- S3105DEFActual EXIT=0.

## S3070ZSquare / S3072ZSquare

- S3070ZSquareActual: NOT actual; fresh EXIT=1. Named gap: Quiver/instance split; `z² = 1`
  must be a conditional input. First errors: `calc` failed to synthesize `Trans Eq Eq`;
  unsolved `z ≫ z ≫ ChartZ = z ≫ z ≫ E37ProjChartZMap ...` (abbrev/G type path).
- S3072ZSquareActual: NOT actual; fresh EXIT=1; line 54 type mismatch between
  `Eq (... ⟶ S2820E37ProjectiveScheme ...)` and `Eq (... ⟶ G)`, line 59 rewrite
  `ChartZ ≫ βs` not found. Existing olean stale; do not cite.

## S3074/S3075/S3078 phi series

- Lead status: S3074PhiFixesK zOver ACTUAL to preserve; phi fixes series INVALID/待修.
- Independent scan: S3074 current source does NOT reproduce (EXIT=1) and old `.out` has
  sorryAx; S3075/S3078 sources are absent and their `.out` logs have sorryAx.
- Until a fresh sorryAx-free olean is produced, do not cite S3074 zOver as ACTUAL;
  record the discrepancy.

## Q' status

- Active Q' = S3078 target; compile pass ACTUAL.
- Still missing: mapComp NatIso, five coherence proofs, IsStack.

## Rule

Any `sorryAx` in `#print axioms` invalidates the declaration for ACTUAL/citable status.
Re-run `lake env lean -o` and `#print axioms` before restoring any of the files above.
