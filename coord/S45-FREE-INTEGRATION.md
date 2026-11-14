# S45-free integration into the final: exact dependency

Date: 2026-11-14. Lane: stage4. **Read-only analysis; no Lean file modified or added.**

## Final targets inspected

- `Mzk1P0FinalS3137ConditionalActual.finalPaperNormalizedComparison`
  `(S : S45SourceFields T) : paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T`
- `Mzk1P0FinalS3137DictionaryActual.finalDictionaryCombined`
  `(S : S45SourceFields T) (rel) (lock) : paper comparison ∧ rel ∧ Nonempty Dictionary`
- `S45SourceFields T = Nonempty (PaperSourceCorrectionFreeFields T)`, fields
  `normRatio_one : ∀ b, qVFamNormRatio T b = 1` and
  `rootHull_scaling : ∀ b, RootHullScalingFormulaAt T b`.

## Two independent S45-free routes

### Route A (sufficient for the final paper inequality): correction-sign route

The current comparison with correction is unconditional
(`BadPlacePaperNormalizedActual.paperNormalizedComparison_with_correction`):
```
paperNormalizedThetaSum ≤ paperNormalizedQPilotSum + paperNormalizedCorrection,
paperNormalizedCorrection = halfNormRatioCorrectionSum - normRatioCorrectionSum,
halfNormRatioCorrectionSum = normRatioCorrectionSum / (2l),
normRatioCorrectionSum = Σ_b nativeBadLocalWeight_b * log(qVFamNormRatio_b).
```
Hence
```
paperNormalizedCorrection = normRatioCorrectionSum * (1/(2l) - 1).
```
`nativeBadLocalWeight_b ≥ 0` (`badPlaceNativeBadLocalWeight_nonneg`), and the
donor power formula gives `qVFamNormRatio_b ≥ 1`:
```
‖q‖_norm = ‖q‖_def^(1/d),  0 < ‖q‖_def < 1,  d = [K_v:Q_p] ≥ 1
⇒ ‖q‖_norm ≥ ‖q‖_def  ⇒ qVFamNormRatio ≥ 1  ⇒ log(qVFamNormRatio) ≥ 0.
```
Therefore `normRatioCorrectionSum ≥ 0`; since `l ≥ 5`, `1/(2l)-1 < 0`, so
`paperNormalizedCorrection ≤ 0`.  Then the green lemma
`BadPlaceNormRatioSourceActual.paperNormalizedComparison_exact_of_correction_nonpos`
gives
```
paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T
```
with **no S45 field** (not `normRatio_one`, not `rootHull_scaling`).

Exact dependency of Route A:
1. `GeneralNormalizedNormBySpectralUniqueness.generalNormalizedNormFormula` (green),
   restricted to `q ≠ 0`; plus the default norm formula
   `FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow`/`logNorm_eq_absNorm_mul`
   and `qNorm_lt_one` for q to identify `‖q‖_def < 1`.
2. `relativeCompletionDegree_pos` (green) for `d ≥ 1`.
3. `QVFamNormalizedCoefficientBridgeActual.qVFamNormRatio` definition and
   `QVFamNormalizedGenerator_norm` (or donor formula directly) for the power comparison.
4. `badPlaceNativeBadLocalWeight_nonneg` for the weight sign.
5. Algebra: `twoL_mul_halfNormRatioCorrectionSum` + `paperNormalizedCorrection_eq`
   for the factor `1/(2l)-1 < 0` (`l.ge_five`).
6. Green `paperNormalizedComparison_exact_of_correction_nonpos`.

New lemmas needed: `qVFamNormRatio_ge_one`, `normRatioCorrectionSum_nonneg`,
`paperNormalizedCorrection_nonpos`, and a wrapper
`finalPaperNormalizedComparison_noS45`.  No new axiom/assumption; this route uses only
green donor/default-norm facts and the existing correction formula.

### Route B (q^d scaling-data route): integration scope

The q^d construction (`g := qVFamNormalizedGenerator^d`, `‖g‖_norm = p^(-paperCoeff)`)
produces `ArithmeticTuplePureFractionalScalingData` at the **qVFam paper coefficient**
via `FinitePlaceStepVAssembly.arithmeticTuplePureFractionalScalingData_ofGenerator`.
Its downstream consumers (for a volume identity) are the Haar-volume theorems
`arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator`
and StepV scaling-data consumers, not the scalar `paperNormalizedComparison`.

Exact dependency of Route B:
1. donor `generalNormalizedNormFormula(q) (q≠0)` + `norm_pow`
   → `‖qVFamNormalizedGenerator^d‖ = p^(-paperCoeff)`;
2. equality `paperCoeff = d * c_norm` (from the green bridge
   `c_norm = paper - log(qVFamNormRatio)/log p q` plus the donor ratio formula);
3. `arithmeticTuplePureFractionalScalingData_ofGenerator`;
4. if used for volume: `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic`.

Route B does **not** feed the current final scalar comparison: that comparison is a
coefficient/weight inequality and never sees a scaling datum.  It also does not fill
`Mzk1MinimalAcceptance.LambdaG_normalizedLogVolume`, which requires data at
`paperRootCoefficientFamily = order/(2l)` (a different coefficient from qVFam
`paperNormalizedCoefficient`); nor S3137 R2's normalized 2l-th-root supply.

## Recommended final dependency substitution

Replace, in the paper side of the final:
```
finalPaperNormalizedComparison (S : S45SourceFields T)
```
by
```
finalPaperNormalizedComparison_noS45 :
  paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T
```
whose proof is exactly Route A.  `finalDictionaryCombined` can then drop its `S`
argument for the paper inequality (the returned `rel`/`Dictionary` never use `S`).

Keep `S45SourceFields` only where correction-**zero**/strict equality is required
(`PaperXiFTargetStrict`, `paperNormalizedComparison_exact_of_strict`, S3137 R2), not
for the final inequality.

## Bottom line

- The final paper inequality can be made S45-free via the **correction-sign route**
  (donor ⇒ ratio ≥ 1 ⇒ correction ≤ 0), not via the q^d scaling datum.
- The q^d scaling route is real but orthogonal to the current final scalar target;
  it feeds volume/hull objects and needs the separate root-coefficient supply for
  minimal acceptance/S3137 R2.
- Exact dependency for final: donor formula + default norm q<1 + d≥1 + weight nonneg +
  l≥5 → correction nonpos → `paperNormalizedComparison_exact_of_correction_nonpos`.

No Lean changes made.
