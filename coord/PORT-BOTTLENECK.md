# PORT-BOTTLENECK — priority 16-file chain: missing oleans, compile estimates, ETA

Status: READ-ONLY analysis, 2026-11-12. No compile.
Sources: tmp/lana_tgfree_waves.json (103 waves), dag/watchdog/watchdog.log,
tmp/priority_files.txt, coord/LANA-PORT-TARGETS-V2.md, coord/PORTED-DECL-STATUS.md.
Scope assumption: the priority chain is the 16-file B1-B16 chain of
LANA-PORT-TARGETS-V2 section 2, which is the minimal LocalConstruct chain for
componentVol/leastHull/archDefect/ind2Term:

  B1  Iut/Concrete/LocalTheory.lean
  B2  Iut/Concrete/LocalConstruct/Packet.lean
  B3  Iut/Concrete/LocalConstruct/Arithmetic.lean
  B4  Iut/Concrete/LocalConstruct/Integral.lean
  B5  Iut/Concrete/LocalConstruct/Indeterminacy.lean
  B6  Iut/Concrete/LocalConstruct/MaximalOrder.lean
  B7  Iut/Concrete/LocalConstruct/Archimedean.lean
  B8  Iut/Concrete/LocalConstruct/Volume.lean
  B9  Iut/Concrete/LocalConstruct/TensorIntegral.lean
  B10 Iut/Concrete/LocalConstruct/ScaleVolume.lean
  B11 Iut/Concrete/LocalConstruct/LocalLogShell.lean
  B12 Iut/Concrete/LocalConstruct/LogShell.lean
  B13 Iut/Concrete/LocalConstruct/Admissible.lean
  B14 Iut/Concrete/LocalConstruct/ThetaAdmissible.lean
  B15 Iut/Concrete/LocalConstruct/LogLattice.lean
  B16 Iut/Concrete/LocalConstruct/FactorShell.lean

plus the staged prerequisite Iut/Concrete/ThetaLocalConstruct/Ordp.lean.
If the intended 16 files are the first 16 entries of tmp/priority_files.txt
instead, the raw closure is much larger (44-57 missing per target; see section 6).

## 1. Current green state of the ported root

Ported source: tmp/external/ported/lana_tgfree/.
OLean root: .lake/build/lib/lean/tmp/external/ported/lana_tgfree/.
Currently: 61 green oleans out of 334 ported source files.

Green in the B chain:
- B11 LocalLogShell: olean YES;
- B15 LogLattice: olean YES (depends only on LocalLogShell);
- Haar (B8 dependency): olean YES.
Missing in the chain:
- Ordp (staged prerequisite) and 14 of the 16 B targets:
  B1,B2,B3,B4,B5,B6,B7,B8,B9,B10,B12,B13,B14,B16.
- B11/B15 are already green (do not recompile).

## 2. Wave/index and missing prerequisite oleans (staged D1/D2)

D1: LocalTheory import Iut.Cor312.Statement -> Mathlib.
D2: Ordp uses only the lower block, imports Mathlib + LocalTheory; drop
EmbedCompletion and Cor312.ThetaData.AdmissiblePrime.
Under D1/D2 the chain is a DAG with the following immediate missing prerequisites:

| order | file | JSON wave | green? | immediate missing prerequisite(s) | est. compile |
|---|---|---|---|---|---|
| 1 | Iut/Concrete/LocalTheory | 19 | no | none after D1 | 45-75s |
| 2 | Iut/Concrete/ThetaLocalConstruct/Ordp | 20 | no | LocalTheory (after D2) | 150-240s |
| 3 | Iut/Concrete/LocalConstruct/Packet | 20 | no | LocalTheory | 240-360s |
| 4 | Iut/Concrete/LocalConstruct/Arithmetic | 21 | no | Ordp | 100-170s |
| 5 | Iut/Concrete/LocalConstruct/Integral | 21 | no | Packet | 180-280s |
| 6 | Iut/Concrete/LocalConstruct/Indeterminacy | 22 | no | Integral | 70-120s |
| 7 | Iut/Concrete/LocalConstruct/MaximalOrder | 23 | no | Indeterminacy | 150-230s |
| 8 | Iut/Concrete/LocalConstruct/Archimedean | 24 | no | MaximalOrder | 160-250s |
| 9 | Iut/Concrete/LocalConstruct/Volume | 25 | no | MaximalOrder, Archimedean; Haar green | 120-200s |
| 10 | Iut/Concrete/LocalConstruct/TensorIntegral | 26 | no | Volume, Arithmetic | 100-170s |
| 11 | Iut/Concrete/LocalConstruct/Admissible | 26 | no | Volume | 90-150s |
| 12 | Iut/Concrete/LocalConstruct/ThetaAdmissible | 27 | no | Admissible | 70-120s |
| 13 | Iut/Concrete/LocalConstruct/ScaleVolume | 27 | no | TensorIntegral | 80-140s |
| 14 | Iut/Concrete/LocalConstruct/LogShell | 28 | no | Arithmetic, ThetaAdmissible, LocalLogShell(green) | 210-340s |
| 15 | Iut/Concrete/LocalConstruct/FactorShell | 29 | no | LogShell, LogLattice(green) | 90-150s |
| - | B11 LocalLogShell | 0 | YES | - | already green |
| - | B15 LogLattice | 1 | YES | LocalLogShell | already green |

Total missing oleans for the chain: 15 (Ordp + 14 B targets).
If the 16 targets are counted without Ordp, B11/B15 are green and 14 targets
remain; the 16th slot is the staged Ordp prerequisite.

## 3. Compile-time calibration

From dag/watchdog/watchdog.log, all DONE lana_tgfree entries with source sizes:
- median observed ratio: about 9.45 s/KB;
- mean is misleading (heavy imports): about 38 s/KB;
- observed heavy examples:
  - LocalLogShell 464s (5.1KB source, heavy import context);
  - Cor312 PacketPresentation 752s (7.5KB);
  - Cor312 RationalPlace 837s (2.0KB);
  - Tower IntegralModel 414s (4.2KB);
  - LogVolume 79s.
For the B-chain estimates above I used size * 6-10 s/KB plus a 30-60s
import/elaboration floor, rounded into ranges. These are estimates, not
measurements; first errors can add triage time.

Expected serial compute:
- sum of midpoints: about 36-40 minutes for 15 files;
- realistic with variable load/heavy imports: 60-100 minutes;
- plus first-error triage (likely 1-3 files need source adaptation): add 20-40
  minutes. Initial ETA after start: 1.5-2.5 hours serial, 2-4 hours including
  fixes.

## 4. Critical path and parallelism

Critical path (staged D1/D2):
  LocalTheory -> Ordp -> Arithmetic -> LogShell -> FactorShell
  plus the longest prerequisite branch:
  LocalTheory -> Packet -> Integral -> Indeterminacy -> MaximalOrder ->
  Archimedean -> Volume -> TensorIntegral -> ScaleVolume -> LogShell -> FactorShell.
This is almost serial: the chain length dominates. Parallel opportunities:
- After LocalTheory: Ordp and Packet can build in parallel (two workers).
- After Volume: TensorIntegral and Admissible can build in parallel.
- After TensorIntegral and Admissible: ScaleVolume and ThetaAdmissible can
  build in parallel.
- LogShell waits for Arithmetic + ThetaAdmissible + LocalLogShell; FactorShell
  waits for LogShell + LogLattice.
Recommended 3-4 watchdog lanes:
  Lane A (critical): LocalTheory -> Ordp -> Arithmetic -> (wait) -> LogShell -> FactorShell.
  Lane B: Packet -> Integral -> Indeterminacy -> MaximalOrder -> Archimedean -> Volume.
  Lane C: after Volume: TensorIntegral -> ScaleVolume.
  Lane D: after Volume: Admissible -> ThetaAdmissible.
Lane A/B are the serial spine; C/D save only the two branch steps. With 3 lanes
the critical path is roughly unchanged; expected wall time ~1.5-2.5 hours plus
triage, because most files are on the spine.

## 5. First bottleneck: D1/D2 staging, not Lean elaboration

The current ported files are NOT decoupled:
- LocalTheory imports Iut.Cor312.Statement (wave 18), whose closure adds
  Anabelian/ThetaData/Torsion/Tower files (44 missing in the current raw
  closure of LocalTheory);
- Ordp imports EmbedCompletion (wave 5) and Cor312.ThetaData.AdmissiblePrime
  (wave 2), exploding the closure to 44-57 missing files depending on target.
Without applying D1/D2, the 16-file chain does not compile in 1-3 hours: the raw
closures require 44-57 additional oleans per target, including the TG-adjacent
chain. This is the actual port bottleneck.
Action: apply D1/D2 to the staging source before any watchdog batch; verify with
closure_analyze.mjs that the closure of B1-B16 contains no Cor312.Statement,
ThetaData, Anabelian.Tempered/GenuineEtale, or TG modules.

## 6. If the intended 16 are tmp/priority_files.txt entries 1-16

First 16 of tmp/priority_files.txt:
  Gap, Forms, Basic, Concrete/Literal, Concrete/LocalEstimate,
  Concrete/SectionAverage, Concrete/TorsionFieldGalois, Cor312/ThetaData/Basic,
  Anabelian/Torsion, Cor312/ThetaData/LocalConditions,
  Cor312/ThetaData/Orbicurve, Anabelian/GenuineEtale, Anabelian/Tempered,
  and the first three TFT files TateFlatAlgebraization, TateFibre,
  NodeEtaleGlueRegular.
Their raw closures are much larger: Gap/Forms/Basic depend on Cor312.Statement
and WallEquiv closure; ThetaData.Basic is wave 16, LocalConditions wave 13,
Orbicurve wave 12, GenuineEtale wave 11, Tempered wave 8; the three TFT files
are in TemperedFundamentalGroups and have no oleans at all. This set is not a
1-3 hour chain; it is a multi-day port including TG-adjacent modules. If this is
the intended meaning, the bottleneck is the Cor312.Statement/ThetaData/Anabelian/
Tempered closure, not the LocalConstruct B chain.

## 7. ETA and recommendation

For the B1-B16 LocalConstruct chain after D1/D2:
- remaining oleans: 15 (Ordp + 14 targets; B11/B15 green);
- serial compute: ~40 min ideal / 60-100 min realistic;
- wall ETA with 3-4 lanes and triage: 2-4 hours;
- hard prerequisites: D1/D2 staging, PadicLogVolume oleans (green), Mathlib.

For the raw priority_files 1-16 set:
- missing closure is hundreds of files including TG-adjacent/TFT;
- ETA: multi-day; not a watchdog scheduling fix. Must first choose a TG-free
  chain, or stage/decouple as in LANA-PORT-TARGETS-V2.

Recommendation: execute B1-B16 after D1/D2; use the wave order above; do not
spend parallel lanes on the two green files; treat raw priority_files 1-16 as a
different, TG-blocked program.

No compile was run; no ETA is a measured promise.
