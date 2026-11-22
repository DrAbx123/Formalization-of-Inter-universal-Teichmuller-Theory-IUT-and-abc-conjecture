# S641: existing paper root hull qPilot comparison (no new carrier)

Date: 2026-10-29. Uses existing root hull/root theta objects.

## Actual comparison (existing)

PaperLevelXiFTargetProofActual:
  globalQPilotLog T <= globalThetaHullLog T.

Here qPilot uses normalized c_norm, Theta uses root c_norm/(2l).
This is the actual per-b containment inequality qPilotNormRegion ⊆ rootNormHull,
summed with nonnegative native weights; no hypotheses.

## Exact formula gap

S641PaperRootHullFormulaGapRequired :=
  forall b, Nonempty (PaperRootHullFormulaGap T b),

i.e. paperRootThetaHullLog T b mu = paperRootThetaFormulaLog T b.
No inhabitant is provided; closure of the union hull is not asserted equal to
the minimal fractional-lattice region.

## Paper qPilot coefficient correction (existing)

s13QPilotCoefficientSum T =
  paperQPilotCoefficientSum T + qCorrectionSum T.

Thus the actual c_norm qPilot comparison is not silently identified with the
paper order(q_v) qPilot; the correction is explicit.

No new carrier/procession; no realThetaValue; no fake equality.
