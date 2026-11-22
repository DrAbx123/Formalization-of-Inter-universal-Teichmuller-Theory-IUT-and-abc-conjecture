# XIF source construction — Stage 1

Date: 2026-10-28. User directive: construct xi-f from the source; prove missing theorems and build missing objects; no simplification/bypass.

## Source anchor

- IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f), corpus lines 10843-10898.
- `-|log(q)|` q-pilot log-volume; `R^{<= -|log(Theta)|}`; inclusion in Step (xi-f).

## Actual Lean carrier used

- `tmp/sheaf/xif/SourceXiFConstruction.lean` (EXIT0, no sorry/axiom):
  - `sourceQPilotPoint v R n := I.sourceThetaPilotPoint v R n (oneSignedLabel l)`
  - `sourceQPilotLogVolume := I.sourceLocalLogDegree v (sourceQPilotPoint ...)`
  - `sourceThetaHullLogValueSet := sourceLocalLogDegree '' sourceHolomorphicHull`
  - `sourceThetaHullLogVolume := sSup sourceThetaHullLogValueSet`
  - `sourceXiFInclusion`: q-pilot log-volume <= Theta-hull log-volume, from actual hull membership; boundedness from `hq <= 1` + `hScaling`.

## Open exact hypotheses at base

1. `hq : (I.theaterAt 0 0).thetaPacket.q <= 1` — source q-contraction status (XIF-6).
2. `hScaling : forall s in sourceScalingUnits, sourceLocalLogDegree s <= 0` — paper Remark 3.9.5 contraction condition (XIF-5).
3. Normalized q-pilot and paper `-|log q|` identification (XIF-1).
4. Theta-hull signed volume/paper `-|log Theta|` identification (XIF-2).
5. `Cor312ComparisonData`/signed certificate consumption (XIF-3/XIF-4).

## Task split (shared board)

- task-485 XIF-1 q-pilot normalized log-volume — qside — `tmp/sheaf/xif/XiFQPilot.lean`
- task-486 XIF-2 theta-hull signed log-volume — volumedet — `tmp/sheaf/xif/XiFHullVolume.lean`
- task-487 XIF-3 xi-f inclusion/comparison data — multiradial (blocked by 485/486)
- task-488 XIF-4 certificate/Cor312 consumption — iplsheapt (blocked by 487)
- task-489 XIF-5 source scaling contraction status — logdescent
- task-490 XIF-6 source q-contraction status — kummer
- task-491 XIF-7 source-fidelity audit — transport
- task-492 XIF-8 assembly/compile gate — primespine (blocked by 485-488)

## Status

- Stage 1 source decomposition: complete for the value/signed carrier route.
- Stage 2: base statements compile; per-task statements in progress.
- Stage 3: base inclusion proved under explicit hq/hScaling; no unconditional claim yet.
- No final acceptance: hq/hScaling source proofs or exact obstructions still required.