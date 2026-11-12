# QPilot L-carrier chain (A935)

## Why the old schema is impossible

`CompletionRootBlock` (S1391:146) requires `NatRootSystem (concreteQUnit ...)` in the
completion; `completionRootBlock_nonempty_iff` (S1391:221) records the obstruction (finite
p-power roots of unity in the completed unit group).  Hence the old single-completion tower
schema cannot be inhabited.

## L-carrier replacement (green)

- `SourcePilotRegionDataL` (S1391:244): the algebraic-closure carrier, with roots,
  Galois-indexed Kummer class/root change, and the diagonal tensor landing;
- `sourcePilotRegionLToCore` (S1391:285): core extraction;
- `actualSourcePilotRegionDataL` (S1391:329): the actual L-side data (green constructor).

## Lean file

`tmp/sheaf/xif/paper/Mzk1QPilotLineLActual.lean`:
- `QPilotLineActualL` (C1, C2, C3L); `PaperQPilotObjectActualL`;
  `QPilotIdentificationActualL` (L versions of the paper identification);
- `qScalar` / `qScalar_neg` / `qScalar_eq_neg_magnitude` from the L core q;
- `qPilotIdentificationActualL_nonempty_of_object`: any L paper object gives Nonempty
  identification (the one-zero part is canonical);
- `qPilotLineActualL_nonempty_of_fields`: reduces line inhabitation to C1/C2/C3L.

## Status / gaps

- C3L is inhabitable via `actualSourcePilotRegionDataL` (green);
- C1 (`SourceInputBinding`) and C2 (`SourceLogKummerData`) constructors are the remaining
  source obligations (C1 had no green T-constructor in earlier audits; C2 has green arrows
  for other carriers);
- `q.order` for a concrete l=5 carrier could not be computed in this pass (needs a concrete
  C3L instance + C1/C2); recorded as the next step.
