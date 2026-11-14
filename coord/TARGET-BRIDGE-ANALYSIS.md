# Target bridge analysis: paper-normalized comparison vs actual magnitude target

Date: 2026-11-14. Lane: stage4. **Read-only analysis; no Lean file modified or added.**

## File / theorem chain

`tmp/sheaf/xif/paper/BadPlacePaperNormalizedTargetBridgeActual.lean` connects
`paperNormalizedThetaSum ≤ paperNormalizedQPilotSum` to the actual target
`actualThetaHullMagnitudeRoot ≤ actualQPilotMagnitudeClassical`.

Exact green bridges in that file:
```
actualQPilotMagnitude_eq_s13Q : actualQPilotMagnitudeClassical = s13QPilotCoefficientSum
paperNormalizedQPilotSum_eq_actual_add_normRatio :
  paperNormalizedQPilotSum = actualQPilotMagnitudeClassical + normRatioCorrectionSum
paperNormalizedThetaSum_eq_s13Theta_add_halfNormRatio :
  paperNormalizedThetaSum = s13ThetaCoefficientSum + halfNormRatioCorrectionSum
ThetaHullCoefficientScalarBridge :
  actualThetaHullMagnitudeRoot = s13ThetaCoefficientSum
paperComparison_iff_actualMagnitude_add_correction :
  paperTheta ≤ paperQPilot  ↔
    actualTheta ≤ actualQ + (normRatioCorrectionSum - halfNormRatioCorrectionSum)
actualTargetMagnitude_of_paperComparison (hbridge) (hcorr) : actualTheta ≤ actualQ
  where hcorr : normRatioCorrectionSum ≤ halfNormRatioCorrectionSum
```
Recall `halfNormRatioCorrectionSum = normRatioCorrectionSum / (2l)`, so
`normRatioCorrectionSum - halfNormRatioCorrectionSum = normRatioCorrectionSum * (1 - 1/(2l))`.

## Direction / sign analysis

With l ≥ 5 and `1 - 1/(2l) > 0`, the correction term in the actual-target
equivalence has the **same sign as `normRatioCorrectionSum`** (positive when the
qVFam normalized norm dominates the default norm).  Therefore:

- `actualTargetMagnitude_of_paperComparison` needs
  `normRatioCorrectionSum ≤ halfNormRatioCorrectionSum`, i.e.
  `normRatioCorrectionSum * (1 - 1/(2l)) ≤ 0`, i.e. `normRatioCorrectionSum ≤ 0`
  (since the factor is positive).
- With nonnegative weights, `normRatioCorrectionSum = Σ_b w_b log(qVFamNormRatio_b)`;
  so `hcorr` is equivalent (pointwise, absent zero-weight degeneracies) to
  `qVFamNormRatio_b ≤ 1` at every bad place.

But the donor now proves the **opposite** bound:
```
qVFamNormRatio_ge_one : 1 ≤ qVFamNormRatio_b
```
so `hcorr` forces `qVFamNormRatio_b = 1` (for positive weights), i.e. exactly the
S45 equality / local degree-one case.  For d > 1 the donor gives ratio > 1, so
`hcorr` is false and the target bridge cannot be invoked.

## Consequence for the S45-free Route A

Route A proves the **paper-normalized scalar inequality**
`paperTheta ≤ paperQPilot` for ratio ≥ 1 (correction in the paper normalization is
nonpositive).  That is the *opposite* sign from what the actual-target bridge needs:
```
paper normalization correction = half - norm      (≤ 0 for ratio ≥ 1, Route A),
target bridge correction     = norm - half      (≥ 0 for ratio ≥ 1).
```
Hence Route A does **not** remove S45/d=1 from the actual magnitude target through
this bridge.  The target bridge is an `if and only if` with a positive correction for
d > 1; paper comparison alone is weaker than the actual target in that regime.

## Current alternatives for the actual target

1. **S45 / d=1 route**: `qVFamNormRatio = 1` gives zero correction, so
   `paperComparison_iff_actualMagnitude_add_correction` reduces the paper comparison
   exactly to the actual magnitude target; this still needs the S45 source condition
   (or a proof that all local degrees are 1).
2. **Model route (already present, but flagged)**:
   `actualPaperXiFTargetMagnitude_actual` is proved from
   `PaperLevelXiFTargetBridgeActual.actualPaperXiFTarget`, which P7 gate notes relies on
   the *model* `PaperLevelXiFTargetProofActual.globalQPilotLog_le_globalThetaHullLog`
   (c_norm/(2l) coefficients); it is not the paper-faithful target bridge.
3. **New route needed for d > 1**: prove a direct actual-target inequality, or a
   correction-controlled statement with the **positive** correction, not via the
   paper-normalized Route A comparison.

## Exact dependency summary

Route A (paper inequality, S45-free):
```
donor qVFamNormRatio_ge_one + weight nonneg + l≥5
  → normRatioCorrectionSum_nonneg
  → paperNormalizedCorrection_nonpos
  → paperNormalizedComparison_exact_of_correction_nonpos
  → paperTheta ≤ paperQPilot
```
Target bridge (actual magnitude, needs S45/d=1):
```
paperComparison_iff_actualMagnitude_add_correction (ThetaHullCoefficientScalarBridge)
  + hcorr : normRatioCorrectionSum ≤ halfNormRatioCorrectionSum
  (⇔ normRatioCorrectionSum ≤ 0 ⇔ ratio ≤ 1; with donor ratio ≥ 1, ⇔ ratio = 1)
  → actualThetaHullMagnitudeRoot ≤ actualQPilotMagnitudeClassical
```

**Conclusion:** the S45-free Route A cannot be transferred to the actual target via
`BadPlacePaperNormalizedTargetBridgeActual`; for d > 1 the correction has the wrong
sign.  The target bridge still requires S45 (ratio = 1) or the local-degree-one case;
the existing model route is a separate, flagged path.

No Lean changes made.
