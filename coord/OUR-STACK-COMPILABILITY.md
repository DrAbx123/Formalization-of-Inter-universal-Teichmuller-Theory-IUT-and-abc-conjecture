# OUR-STACK-COMPILABILITY — olean/import-closure audit (A1040)

Status: read-only file/olean audit, **no compile**.  Checked 2026-11-13 (turn 384).
Method: for each target module, resolved source/olean under `D:/lean/` and
`D:/lean/.lake/build/lib/lean/`, then walked imports recursively (Mathlib/Lean
toolchain imports skipped for the dependency listing).

## 1. Target files and oleans

All 14 targets have both a source file and a fresh olean (olean mtime newer than
source; no stale flag):

| target | file | olean | direct imports |
|---|---|---|---|
| `Mzk1PaperStepVBoxActual` | yes | yes | Mathlib.Tactic |
| `Mzk1DExactLowerActual` | yes | yes | ThetaDataLegality, LocalVolumeAssembly, KappaLemma |
| `Mzk1DExactFromHullActual` | yes | yes | Mathlib.Tactic |
| `Mzk1PaperNormDeficitActual` | yes | yes | PaperNormMu, PaperNormTheta |
| `Mzk1StepVIdentificationActual` | yes | yes | StepVVolumeUpper |
| `Mzk1StepVVolumeUpperActual` | yes | yes | Mathlib.Tactic |
| `Mzk1VStepVAlignmentActual` | yes | yes | Mathlib.Tactic |
| `Mzk1LocalVolumeAssemblyActual` | yes | yes | Mathlib.Tactic |
| `Mzk1ThetaDataLegalityActual` | yes | yes | PrimeConductorRoute |
| `Mzk1KappaLemmaActual` | yes | yes | Mathlib.Tactic |
| `Mzk1SSIneqExplicitFormActual` | yes | yes | Mathlib.Tactic |
| `Mzk1DeficitSignActual` | yes | yes | DifferentDictionary, PaperNormDeficit |
| `Mzk1DifferentDictionaryActual` | yes | yes | LeanFormal LocalFields (2 modules) |
| `Mzk1P2DeficitActual` | yes | yes | PaperNormDeficit, PaperNormMu |

No target has a missing olean or source-newer-than-olean.

## 2. Import closure: own green vs external

Recursive closure of the 14 roots: 137 nodes, **0 missing oleans**; no `Iut`/TG
failure.  The closure is not literally only our own `Mzk1*` files: it also includes
green `LeanFormal.*`, `tmp.sheaf.n8.*`, `tmp.sheaf.xif.*` modules and one lana-root
module.

### 2.1 Internal/our-tree modules (all olean present)

- `tmp.sheaf.xif.paper.Mzk1*` (the target files themselves plus their Mzk1 deps:
  `Mzk1PrimeConductorRouteActual`, `Mzk1FinalBoundarySzpiroActual`,
  `Mzk1ShellCoeffComputationActual`, `Mzk1N3SharedContainerBridgeShaActual`,
  `Mzk1PaperNormMuActual`, `Mzk1PaperNormThetaActual`,
  `Mzk1ShellArithmeticIdentitiesActual`, ...).
- `tmp.sheaf.n8.closure.C9Paper`, `SourceWitnessedOutput`, `SourceInputBinding`,
  `SourceLogKummerRealization`, `SourcePilotRegion`, `C6ActualIQData`.
- `tmp.sheaf.xif.PaperQPilotLogVolume`, `PaperXiFInclusion`, `PaperQPilotObject`,
  `PaperSignedHull`.
- `tmp.sheaf.xif.paper.QPilotObjectActual`, `QPilotScalarIdentificationActual`,
  `PaperLineBundleCarrierBase`, `PrimeStripLogShellActual`,
  `C3LogShellTensorPacketActual`.

### 2.2 Green `LeanFormal.*` modules (all olean present)

Key groups:
- `IUTIII.Corollary312.StepXI.HolomorphicHull.*` (SourceImageHull,
  SourceImageHullVolume, SourceQSideComparison, IQCarrierHaarData,
  HullDeterminantLogVolumeReduction, IQCarrierConcreteModel,
  SourceHullCompactnessReduction, LocalFieldProductHull, ...);
- `IUTIII.Theorem311.*` (SourceOriginalInput, SourceProcessionBoundary,
  SourceKummerEvaluationArrows, SourceArithmeticHolomorphicLanding,
  SourceH1H2Construction, ParametricDStage, ConcreteRouteNormalForm,
  SourceFTimesMuPrimeStripPolyIsomorphism);
- `IUTIII.Corollary312.StepXI.*` (Contract, ContractSourceReduction,
  ParametricStepXI, FiniteCertificateBridge, Volume, SourceProcessionStepXI,
  CertificateHullWiring, SourceSharedBoundary);
- `ABCBridge.Geometry.*` (FinitePlaceArithmeticTensorBlocks,
  FinitePlaceIQHull*, FinitePlaceNormalizedUnitScalingLogVolume,
  FinitePlaceCompletionPacket, FinitePlaceArithmeticIQHull, ...);
- `Foundations.LocalFields.*` (LocalDifferent*, IntegralTraceDual*,
  IntegralLogShell*, FinitePadic*, ...);
- `Foundations.NumberField.*`, `Foundations.Arithmetic.*`,
  `Foundations.Theta.*`, `Foundations.MeasureTheory.*`;
- `IUTII.Kummer.*`, `IUTII.Frobenioid.*` (Example36*).

### 2.3 Lana root / TG

- **No TG module** (`TemperedFundamentalGroups`) appears in the closure.
- Exactly one lana-root module appears:
  `Iut.Foundations.Frobenioid` (via `tmp.sheaf.n8.closure.SourceInputBinding`),
  olean present.  This is a residual lana dependency but not a blocker locally.
- No closure node has a missing olean; the build should be able to reuse the
  current `.lake` artifacts without rebuilding lana/TG.

## 3. Immediate compile order suggestion

Topological order (leaves first):

1. **Independent leaves** (no target-file deps):
   - `Mzk1PaperStepVBoxActual`
   - `Mzk1DExactFromHullActual`
   - `Mzk1StepVVolumeUpperActual`
   - `Mzk1VStepVAlignmentActual`
   - `Mzk1LocalVolumeAssemblyActual`
   - `Mzk1KappaLemmaActual`
   - `Mzk1SSIneqExplicitFormActual`
   - `Mzk1DifferentDictionaryActual`
2. `Mzk1ThetaDataLegalityActual`
   (needs `Mzk1PrimeConductorRouteActual`; its closure includes SSIneq/Kappa/
   FinalBoundary; all olean present)
3. `Mzk1DExactLowerActual`
   (needs ThetaDataLegality + LocalVolumeAssembly + KappaLemma)
4. `Mzk1StepVIdentificationActual`
   (needs StepVVolumeUpper)
5. `Mzk1PaperNormDeficitActual`
   (needs PaperNormMu + PaperNormTheta; both olean present)
6. `Mzk1DeficitSignActual`
   (needs DifferentDictionary + PaperNormDeficit)
7. `Mzk1P2DeficitActual`
   (needs PaperNormDeficit + PaperNormMu)

`Mzk1DExactFromHullActual` and `Mzk1PaperStepVBoxActual` are already independent
of the Mzk1 stack and can be compiled first; `Mzk1VStepVAlignmentActual` is also
independent.

## 4. Caveats

- Olean presence/provenance is not a proof of `#print axioms` trio; no
  `#print axioms` check was run in this audit (no compile allowed).
- The one lana-root import (`Iut.Foundations.Frobenioid`) means the stack is not
  fully lana-free; if the gate requires a pure LeanFormal tree, that import is
  the only residual lana edge to schedule for porting/removal.
- `Mathlib` oleans are assumed present; they are outside the audit scope.
- No source file was modified and no compilation was performed.
