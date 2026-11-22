# C9 P6 source double-construction comparison (stage-1 design)

Date 2026-10-24. Consumer: C9 Values/Q/Theta and C10 Cor.3.12. No Lean edits.
Source route: C9-ROUTE-CONSISTENCY-REVIEW-20261023.md; C9-STAGE1-SUPPLEMENT-ROUTE.

## Fixed data

(S,L): actual native initial Theta data plus log-theta-lattice (L type still a P0 statement gap).
X : N8NativeInput l is the current Lean entry for S/lattice slice.
A complete source choice is alpha; a fixed J denotes a source-allowed integral structure selection.

## Chain A: native q

A1. S.clauseB native q at a native bad finite place:
  NativeC3.nativeQDonorActual X
  NativeC3.nativeQActual X : FinitePlaceQCandidate (nativeFPlaceOverBad X)
Status: actual (from native Clause (b) Tate comparison witness).

A2. Local q-region/scalar:
  C9QPilotRegion.qPilotRegionSource X = {(nativeQ X).q}
  C9QPilotRegion.qPilotSignedLog X
  C9QPilotRegion.qPilotKummerRelativeVolume X
  C9QPilotRegion.qPilotProcessionNormalizedVolume X
Status: local scalar/region actual; full procession-normalized global volume is conditional
(qPilotProcessionNormalizedVolumeTarget_obligation named sorry).

A3. Q = L_q(Rq):
- need actual global framework readout L_q and identification with the native q scalar;
- current QPaper scalar is not the global L.
Status: OPEN (P2/P6).

## Chain B: algorithm output

B1. Fixed gluing data and complete alpha:
- current C4 has only SourceWitnessedOutputData over old OriginalInput and SignedLabel choices;
- native bridge is missing (C1BridgeProof named donor NativeOldBindingDonorsExist);
- complete alpha/R_alpha source type is MISSING.

B2. Component regions R_alpha,i and union U_i; hull H_i:
- current C4 U is a finite eval point set; source hull is sourceHolomorphicHull;
- no actual component-wise R_alpha,i/H_i with admissible structure;
Status: OPEN (P1/P3).

B3. HullPoss = {R | Adm_out(R) and R subset H}; Values = ell_out image of HullPoss:
- current C9Paper ValuesPaper uses arbitrary provenance/subsets; invalid;
- C9ValuesPaper outputRegion is finite point image, zero-mass; invalid;
Status: OPEN (P3/P4).

B4. Global readout ell_out:
- current C6 normalizedLogVolume is a single tensor block; no global weights/procession/column shifts;
Status: OPEN (P2).

## Comparison proposition (P6)

exists source-allowed J, R_J in HullPoss and ell_out(R_J) = Q
or one-sided: forall epsilon>0, exists R in HullPoss, Q - epsilon <= ell_out(R).

J admissible range must be defined independently of Q, Q<=Theta, or the desired equality.

## Arrow obligations

| id | arrow | source responsibility | current status |
|---|---|---|---|
| A1 | S -> native q | Clause (b) q comparison | actual |
| A2 | native q -> local region/scalar | q-pilot local object | actual partial; global normalization OPEN |
| A3 | local -> Q via L_q | framework readout/calibration | OPEN P2/P6 |
| B1 | S/L -> alpha/R_alpha | complete source output construction | OPEN P1 |
| B2 | R_alpha -> U/H | component union/hull | OPEN P1/P3 |
| B3 | H -> HullPoss/Values | Stp4 admissible enlargement | OPEN P3/P4 |
| B4 | HullPoss -> ell_out | global weighted/procession readout | OPEN P2 |
| C | Q vs ell_out | double-construction comparison | OPEN P6 |

## Next deliverables

1. Exact Lean types for S/L, alpha, R_alpha and component indices; no free fields.
2. Arrow table with actual source theorems/citations for each composite; missing arrows OPEN.
3. Precise P6 statement with J range independent of Q.
4. Only then define QPaper/ValuesPaper/ThetaPaper Lean targets.

## Status

C9 P6 is OPEN. No Lean target accepted; no N8 closure. Current QPaper/ValuesPaper are not source objects.