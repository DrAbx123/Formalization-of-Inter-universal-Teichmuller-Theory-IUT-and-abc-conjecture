# WALL-PORT-FEASIBILITY — external NumericalWall chain (lana iut-main)

Status: READ-ONLY audit, 2026-11-12. No compile.
External source root: tmp/online/lana-agents__iut/iut-main/.
Current ported root: tmp/external/ported/lana_tgfree/.
OLean root checked: .lake/build/lib/lean/tmp/external/ported/lana_tgfree/.

## 1. Existence table

| target | external source | bytes | ported source | olean | verdict |
|---|---|---|---|---|---|
| Iut/Wall/BPS.lean | YES | 17397 | YES | YES 888624 | READY / already green |
| Iut/Wall/Checks.lean | YES | 8754 | YES | NO | blocked (main theorem closure) |
| Iut/Wall/Rss.lean | YES | 26622 | YES | NO | heavy, chain through ThetaRegion |
| Iut/Wall/Pilots.lean | YES | 15331 | YES | NO | heavy, chain through ThetaRegion |
| Iut/Wall/EtaAlg.lean | YES | 12210 | YES | NO | blocked (MainTheorem) |
| Iut/Wall/QPilotRegion.lean | YES | 17698 | YES | NO | blocked (Checks/IdentifiedCopies) |
| Iut/Wall/NumericalWallHull.lean | NO | 0 | NO | NO | MISSING SOURCE |
| Iut/Wall/Ind3.lean | YES | 15065 | YES | NO | heavy, chain through Rss |
| Iut/Wall/IdentifiedCopies.lean | YES | 25480 | YES | NO | blocked (Checks) |

No NumericalWallHull.lean or any *Numerical* / *WallHull* file exists under
tmp/online/lana-agents__iut; the name is not present in that snapshot.

## 2. Dependency closures (external snapshot, local Iut files + external imports)

| target | local Iut closure | external closure | Mathlib | TFT | Pi1 | Tate | Padic | Other | TG-risk |
|---|---|---|---|---|---|---|---|---|---|
| BPS | 1 | 6 | 6 | 0 | 0 | 0 | 0 | 0 | none |
| Pilots | 144 | 76 | 34 | 32 | 6 | 2 | 2 | 0 | HIGH |
| Rss | 155 | 76 | 34 | 32 | 6 | 2 | 2 | 0 | HIGH |
| Ind3 | 156 | 76 | 34 | 32 | 6 | 2 | 2 | 0 | HIGH |
| EtaAlg | 233 | 91 | 40 | 32 | 7 | 2 | 2 | 8 | HIGH |
| Checks | 234 | 91 | 40 | 32 | 7 | 2 | 2 | 8 | HIGH |
| IdentifiedCopies | 235 | 91 | 40 | 32 | 7 | 2 | 2 | 8 | HIGH |
| QPilotRegion | 236 | 91 | 40 | 32 | 7 | 2 | 2 | 8 | HIGH |

Other external imports (non Mathlib/TFT/Pi1/Tate/Padic) are:
Genl.Curves.ProofPackage, Genl.GeneralPosition.HeightTheory,
Genl.GeneralPosition.TheoremTwoOne, Heights.Local.Bounded,
Heights.TorsionArchimedean, Heights.VariableChangePoint,
Heights.VeluProduct, OrbicurveCores.U2.Assembly.
The exact module TateCurvesTheta also appears as a bare import.
Counts are graph closure counts from the external source imports; they are not
a claim that all listed modules compile in this project.

## 3. Direct chain structure

Imports in the external snapshot:
  BPS: Mathlib only (6 modules).
  Pilots: BPS + Iut.Concrete.ThetaRegion.
  Rss: Pilots + Iut.Concrete.Ind1Invariance.
  Ind3: Rss.
  EtaAlg: Ind3 + Iut.MainTheorem.
  Checks: EtaAlg.
  IdentifiedCopies: Checks.
  QPilotRegion: IdentifiedCopies.
So the NumericalWall chain is:
  BPS -> Pilots -> Rss -> Ind3 -> EtaAlg -> Checks -> IdentifiedCopies -> QPilotRegion.
NumericalWallHull would have to be an additional node, but its source is absent.

## 4. Port feasibility by target

### BPS — feasible, zero work
- local closure 1, all imports Mathlib, no TG, ported olean already exists.
- Reuse directly; no port/compile needed.

### Pilots, Rss, Ind3 — heavy but structurally possible
- closures 144-156 local Iut files, 32 TFT modules, 6 Pi1, 2 Tate, 2 Padic.
- They depend on Iut.Concrete.ThetaRegion (wave 35 in the lana_tgfree wave list)
  and Concrete/Ind1Invariance; ThetaRegion itself depends on ThetaLocalConstruct.Data
  and the Cor312 chain.
- Direct port is NOT a short batch: it requires the ThetaRegion/ThetaLocalConstruct
  chain and external TFT/Pi1/Tate/Padic closures.
- Feasible only after:
  1. a TG-free ThetaRegion/ThetaLocalConstruct extraction (or a declaration-level
     copy with exact types and abstract InitialThetaData context), and
  2. compiling the 32 TFT dependencies (SemistableReduction is RED-risk).
- Estimated scale: hundreds of local files; multi-day/weeks, not hours.

### EtaAlg, Checks, IdentifiedCopies, QPilotRegion — blocked
- all include Iut.MainTheorem through EtaAlg.
- MainTheorem closure is 233-236 local Iut files plus 32 TFT, 7 Pi1, 2 Tate,
  2 Padic, 8 Genl/Heights/OrbicurveCores modules.
- This is the full lana main-theorem closure, not a Wall-only port; direct port
  is NOT feasible in the current phase.
- Minimal alternative: declaration-level copy of the needed Wall statements
  (Checks/Rss/IdentifiedCopies declarations) with an abstract context, as in the
  Phase 4 copy-only manifest; this is a new extraction task, not a compile port.

### NumericalWallHull — absent
- No source file; cannot port or compile.
- If the mathematical statement is required, it must be reconstructed from the
  paper/source or located in another upstream branch; no candidate file in the
  audited snapshot.

## 5. TG and RED risk

Every target except BPS has 32 TemperedFundamentalGroups imports in its external
closure, including SemistableReduction modules. Those are the same external
modules identified as RED/blocked in earlier port audits. Therefore a direct
watchdog port of the Wall chain cannot be scheduled as a short task: it inherits
the TG build risk before any Wall file compiles.

## 6. Recommendation

1. Keep BPS as the only immediately reusable Wall asset (already green).
2. Do not schedule full ports of Pilots/Rss/Ind3/EtaAlg/Checks/IdentifiedCopies/
   QPilotRegion in the current phase; their closures are MainTheorem-scale and
   TG-dependent.
3. For a specific declaration need, use copy-only extraction of the exact
   statement/body with an abstract context (Mzk1Ported pattern), and record all
   unresolved dependencies. Do not import Iut.MainTheorem.
4. Treat NumericalWallHull as MISSING; reconstruct or defer, do not fabricate a
   file under that name.

No Lean file written; no compile claimed.