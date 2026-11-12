# FINAL ASSEMBLY — ABC chain after lana oleans (A809)

Status: 2026-11-11 23:5x UTC+8 (mainline). This file is the executable checklist for the
final assembly once the DAG watchdog has produced the lana `Iut` oleans. Nothing here
is claimed as proved before its compile+gate lines exist.

## 0. Prerequisites (lana oleans, in topological order)

1. Pi1 shim chain for `Iut/Cor312/ThetaData/Basic`:
   `Pi1/Mathlib/RingTheory/Flat/Equalizer` -> `Pi1/RingTheory/KerTensor` ->
   `Pi1/FundamentalGroup/{FiniteEtale,Galois,Functoriality,DenseOpen,Point,GenericPoint}`.
2. Iut chain: `Iut/Cor312/ThetaData/Basic` -> `Iut/Cor312/{LeftHandSide,RightHandSide,Statement}`
   -> `Iut/Concrete/{ThetaLocalConstruct/Data,ThetaRegion,Ind1Invariance}` ->
   `Iut/Wall/{Pilots,Rss,Ind3,MultiContainer,...,EtaAlg,Checks}` -> `Iut/MainTheorem`.
3. Vendor roots used by the above: `TateCurvesTheta/*` (already oleans), `Pi1/*`,
   `FormalSchemes/*`, `CurvesJacobian/*`, `WeilCurves/*`, `Belyi/*`.

Check command:

    Get-Content dag/watchdog/watchdog.log | Select-String 'DONE EXIT=0 Iut/'

## 1. Assembly files and compile commands

Every file is compiled alone, with its own olean:

    lake env lean -R . -o .lake/build/lib/lean/<module path>.olean <file.lean>

| order | file | module | status now | expected gate |
|---|---|---|---|---|
| 1 | `Mzk1SSIneqConsumerChainActual.lean` | `tmp.sheaf.xif.paper.Mzk1SSIneqConsumerChainActual` | PENDING-EXTERNAL (`Iut/WallEquiv/Basic.olean`) | trio |
| 2 | `Mzk1StepXISSIneqDictionaryShaActual.lean` | ... | EXIT=0 + olean (skeleton, fields TODO) | trio |
| 3 | `Mzk1FinalABCBridgeActual.lean` | ... | PENDING-EXTERNAL (`Iut/MainTheorem.olean`) | trio |
| 4 | `Mzk1StepXIMinimalStatementShaActual.lean` | ... | EXIT=0 + olean (lana-free) | trio |
| 5 | `Mzk1StepXIMinimalStatementActual.lean` | ... | PENDING-EXTERNAL (`Iut/Wall/MultiContainer.olean`) | trio |
| 6 | `Mzk1StepXICor312FullAssemblyActual.lean` | ... | EXIT=0 + olean (already green) | trio |
| 7 | `Mzk1Cor312FullActual.lean` (canonical re-export) | ... | EXIT=0 + olean (already green) | trio |

File 1 semantics:

    abcConjecture_of_forall_ssIneq (h : forall D, Iut.Wall.SSIneq D) : ABCConjecture
    cor312VariantHolds_of_forall_ssIneq (h : ...) : Iut.Cor312VariantHolds

via lana `Iut.WallEquiv.classicalABC_of_ss` (Iut/WallEquiv/Basic.lean:180) and our
`Mzk1FinalABCBridgeActual.classicalABC_implies_ABCConjecture`.

## 2. Gates (mandatory)

Each file ends with `#print axioms` on its main theorems; the accepted output is

    depends on axioms: [propext, Classical.choice, Quot.sound]

Anything else (new axiom, sorryAx) stops the assembly. Also check `#print axioms` for the
row-count theorems (expected: no axioms).

## 3. Dependency/expected unlock order

1. `dag_plan` (retry window 180 s) schedules Pi1 shim chain; fix drift as needed
   (see blockers) -> `Pi1/FundamentalGroup/GenericPoint.olean`.
2. Next batch: `Iut/Cor312/ThetaData/Basic` START; then LHS/RHS/Statement.
3. Then `Iut/Concrete/ThetaRegion`, `Iut/Wall/*`, `Iut/MainTheorem`.
4. Then file 1 compiles; file 3 compiles; file 2 gets its fields filled (sC = sFactor (nC D),
   logq = 2*l*D.qPilot.absLogQ, V = logVol D (hullOf D (vcI D))) and links its lana shape.
5. Final report: gates of files 1,3,2,6,7 + `dag_plan` closure/dirty snapshot.

## 4. Current blockers (2026-11-11 23:5x)

* **Pi1 API drift (first real blocker)**: `Pi1/Mathlib/RingTheory/Flat/Equalizer.lean`
  fails at `auxEquivRHS_symm_tmul` proofs: bare `simp` is now `simp made no progress`
  (Mathlib drift); removing it gives an isDefEq heartbeat timeout, and with
  `maxHeartbeats 0` the `exact AlgHom.tensorEqualizerEquiv_symm_apply ..` leaves
  `Module.Flat ?m ?m` typeclass metavariables stuck. Fix attempt in progress (backup
  `Equalizer.lean.bak-a807`); minimal repair must preserve the mathematics and be recorded
  in `Mzk1VendorApiDriftAuditActual`.
* **Chain state**: `Iut/Cor312/ThetaData/Basic` is dirty but still skipped because its
  Pi1/Galois chain is behind it; retry window is now 180 s so deps come back quickly.
* **Watchdog**: single instance, DAG_MAX=10, `dag_plan` retry window 180000 ms;
  last CYCLE pending=549 (16:37Z) after plan reload.

## 5. First-error handling

* missing olean (`object file ... does not exist`): do not patch the consumer; check the
  dependency is in `plan.dirty`; if not, report the module name and wait/touch.
* real Lean error/API drift: vendor file -> patch (backup `.bak-aNNN`), record in vendor
  audit, single-file compile, then continue the chain one step at a time.
* OOM (`std::bad_alloc`): do not lower DAG_MAX; single-process compile of the one file when
  the machine is idle, then resume.
* churn: if SKIP/RETRY ratio explodes after a plan change, revert the plan-side change
  (e.g. priority list) and rebuild.

## 6. Deliverables

* `Mzk1SSIneqConsumerChainActual.olean` + gates trio;
* `Mzk1FinalABCBridgeActual.olean` + gates trio;
* `Mzk1StepXISSIneqDictionaryShaActual.olean` (fields filled) + gates trio;
* `Mzk1StepXICor312FullAssemblyActual.olean`, `Mzk1Cor312FullActual.olean` (already green);
* audit files: `Mzk1G4DictionaryAuditActual`, `Mzk1VendorApiDriftAuditActual`,
  `Mzk1DagImportParserFixActual`, and this checklist.

No canonical target changed; ABC gate NOT passed until the SSIneq input is proved.
