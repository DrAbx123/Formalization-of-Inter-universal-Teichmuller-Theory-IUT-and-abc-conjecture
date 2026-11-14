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

## Route A ratio proof — read-only verification (2026-11-14 14:50)

The ratio proof already exists in
`tmp/sheaf/xif/paper/Mzk1GenericNormBridgeActual.lean` (source; currently no olean):

- `normalized_norm_eq_default_norm_rpow`: for a finite place and `x ≠ 0`,
  `‖x‖_normalized = ‖x‖_default ^ (1/d)`, proved from the donor
  `generalNormalizedNormFormula`, the green default formula
  `norm_eq_absNorm_zpow`, the identity
  `WithZero.log (Valued.v x) = Multiplicative.toAdd (WithZero.unzero ...)`, and
  `Real.rpow_mul`.  This is exactly the carrier/instance bridge that was listed as
  an "explicit remaining gap" in `Mzk1P0S45FreeFinalRouteAActual`.
- `qVFamNormalizedNorm_eq_defaultNorm_rpow`: the qVFam specialization via
  `simpa [qVFamNormalizedNorm, qVFamDefaultNorm, qVFamNormalizedGenerator,
    qVFamTensorPlace, NormalizedCompletion, CommonPrimeCompletion]`.
- `qVFamDefaultNorm_pos`, `qVFamDefaultNorm_lt_one` (from `qNorm_lt_one`).
- `qVFamNormRatio_ge_one`: `1 ≤ qVFamNormRatio T b`, using
  `d = relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b)`,
  `relativeCompletionDegree_pos`, `1/d ≤ 1`, and
  `Real.rpow_le_rpow_of_exponent_ge` (with `0 < default < 1`).

Status caveat: the file currently has **no olean**.  The latest watchdog error is a
stale import error for `Mzk1P0S45FreeFinalRouteAActual` at line 2, but the current
source line 2 is `GeneralNormalizedNormBySpectralUniqueness` and the file does **not**
import RouteA; this is a source/log race, so the proof should be re-run/verified by the
watchdog.  No source change was made.

### Route A wrapper dependency

`Mzk1P0S45FreeFinalRouteAActual` currently fails only at
`:53:16 unknown identifier badPlaceNativeBadLocalWeight_nonneg`.  That theorem is in
`PaperBadPlaceTensorGeometryActual.lean:277`; RouteA must import/open
`PaperBadPlaceTensorGeometryActual` (or qualify the name).  After that:

1. `Mzk1GenericNormBridgeActual.qVFamNormRatio_ge_one`
2. `Mzk1P0S45FreeFinalRouteAActual.normRatioCorrectionSum_nonneg_of_ratio_ge_one`
3. `...paperNormalizedCorrection_nonpos_of_sum_nonneg`
4. `...finalPaperNormalizedComparison_noS45_of_ratio_ge_one`
5. a final wrapper `finalPaperNormalizedComparison_noS45 := ... (qVFamNormRatio_ge_one T)`

Exact import/dependency direction:
`Mzk1GenericNormBridgeActual` → `Mzk1P0S45FreeFinalRouteAActual` → final S3137 files.
Generic does not import RouteA, so no cycle.

### Integration into final

- Replace `finalPaperNormalizedComparison (S : S45SourceFields T)` in
  `Mzk1P0FinalS3137ConditionalActual` by the no-S45 wrapper.
- `finalDictionaryCombined` can drop its `S` argument for the paper inequality;
  `rel`/`Dictionary` never use `S`.
- Keep S45 only for correction-zero/strict equality targets.

Bottom line: the ratio proof is already present and consistent with the donor formula;
the only concrete fixes are (i) watchdog re-run of Generic after the stale import race,
(ii) RouteA import/open of `PaperBadPlaceTensorGeometryActual`, (iii) final wrapper
substitution.  No Lean changes made in this read-only check.

## Generic/RouteA integration status (2026-11-14 15:00, read-only)

Current status:

- `Mzk1P0S45FreeFinalRouteAActual`: **GREEN** (olean 14:55:39).  It proves the
  conditional wrapper
  `finalPaperNormalizedComparison_noS45_of_ratio_ge_one : (∀ b, 1 ≤ qVFamNormRatio T b) →
    paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T`.
- `Mzk1GenericNormBridgeActual`: **NO olean**.  The source was rewritten at 15:00:47:
  it now contains only the **conditional** lemma
  `qVFamNormRatio_ge_one_of_norm_bridge (d : ℕ) (hd : 1 ≤ d)
    (hbridge : qVFamNormalizedNorm T b = (qVFamDefaultNorm T b) ^ (1 / (d : ℝ))) :
    1 ≤ qVFamNormRatio T b`.
  The earlier donor-derived `normalized_norm_eq_default_norm_rpow` /
  `qVFamNormalizedNorm_eq_defaultNorm_rpow` / unconditional
  `qVFamNormRatio_ge_one` are **no longer present** in the current source (search finds
  only the conditional lemma).  Its latest log is stale (line-2 import RouteA and old
  line numbers), while the current source line 2 is
  `QVFamNormalizedCoefficientBridgeActual`; a watchdog re-run of the current file is
  needed.
- `Mzk1P0S45RefutationSchemeActual`: also conditional; needs an explicit
  `hpow : qVFamNormalizedNorm = default^(1/s1915LocalDegree)` plus `1 < d`.

**Integration consequence:** the final S45-free substitution is **blocked on restoring
the bridge lemma**
`qVFamNormalizedNorm T b = (qVFamDefaultNorm T b) ^ (1 / d)`
for `d = relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b)`.  RouteA is already
green; once that bridge is available, the exact chain is:

```
qVFamNormalizedNorm_eq_defaultNorm_rpow (restored)
  → qVFamNormRatio_ge_one (Generic, or instantiate the conditional lemma)
  → Mzk1P0S45FreeFinalRouteAActual.finalPaperNormalizedComparison_noS45_of_ratio_ge_one
  → finalPaperNormalizedComparison_noS45
  → final S3137 paper inequality without S45
```

The bridge proof content from the earlier source was:
1. donor `generalNormalizedNormFormula` for `x ≠ 0`;
2. green `norm_eq_absNorm_zpow` for the default norm;
3. `WithZero.log (Valued.v x) = Multiplicative.toAdd (WithZero.unzero ...)`,
   hence `nu x = -m`;
4. rewrite both formulas and `Real.rpow_mul` to obtain
   `normalized = default^(1/d)`.
It needs imports `GeneralNormalizedNormBySpectralUniqueness` and
`FinitePlaceCompletionNormTransport`, plus the qVFam specialization through
`qVFamNormalizedNorm/qVFamDefaultNorm/qVFamNormalizedGenerator`.

No Lean changes made; this is the exact remaining dependency for Generic/RouteA
integration.

## hbridge proof route (read-only, 2026-11-14 15:10)

Target:
```
qVFamNormalizedNorm T b =
  (qVFamDefaultNorm T b) ^ (1 / (relativeCompletionDegree (k := ℚ)
    (qVFamTensorPlace T b) : ℝ))
```

Exact carrier issue: `qVFamDefaultNorm` lives on the **default** valued adic
completion `C = (qVFamTensorPlace T b).maximalIdeal.adicCompletion F`, while
`qVFamNormalizedNorm` is the norm on `L = NormalizedCompletion place`
(=`CommonPrimeCompletion`), with the spectral instance.  The donor supplies
`toC : L place → C place` (definitionally the identity) and `nu` on `L`; the
green transport file supplies the default norm formula on `C`.

Proof route (all green inputs):

1. Let `x : L place := qVFamNormalizedGenerator T b`; `hx : x ≠ 0` from
   `qVFamNormalizedGenerator_ne_zero`.
2. `hdef := norm_eq_absNorm_zpow (P := qVFamTensorPlace T b) (toC place x) hx'`
   where `hx' : toC place x ≠ 0` is `by simpa [GeneralNormalizedNormBySpectralUniqueness.toC] using hx`.
   This gives `‖toC x‖_C = absNorm ^ m`, with
   `m = Multiplicative.toAdd (WithZero.unzero (Valued.v (toC x)))`.
3. `hnorm := generalNormalizedNormFormula (F := T.arithmetic.F) (qVFamTensorPlace T b) x hx`
   gives `‖x‖_L = absNorm ^ (-(nu place x)/d)`.
4. Log/unzero bridge: with `hv : Valued.v (toC place x) ≠ 0`
   (`valuation_ne_zero_of_ne_zero`), prove
   `WithZero.log (Valued.v (toC place x)) = m` by
   `conv_lhs => rw [← WithZero.coe_unzero hv]; rfl`, hence
   `nu place x = -m` by `unfold nu; rw [hlog]; ring`.
5. Rewrite `hdef` using `qVFamDefaultNorm = ‖(qVFamily T b).q‖` and the
   definitional equality `toC x = (qVFamily T b).q` (or `simpa [toC, qVFamDefaultNorm,
   qVFamNormalizedGenerator]`), so `qVFamDefaultNorm = absNorm ^ m`.
6. Algebra: `absNorm^(-nu/d) = absNorm^(m/d)` (by `hnu`) and
   `absNorm^(m/d) = (absNorm^m)^(1/d)` by `Real.rpow_mul`
   (`absNorm_pos`) plus `Real.rpow_intCast`/`Real.rpow_natCast` as needed;
   hence `qVFamNormalizedNorm = qVFamDefaultNorm ^ (1/d)`.
7. Specialize `d := relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b)`;
   no S45 and no norm equality used.

Exact imports for a new hbridge file:
`GeneralNormalizedNormBySpectralUniqueness`, `FinitePlaceCompletionNormTransport`,
`QVFamNormalizedCoefficientBridgeActual`, `QVFamNormalizedGeneratorSupplyActual`,
`QPilotZeroLocusDivisorActual` (for `qVFamily`/`qNorm_lt_one`), plus
`Mathlib.Tactic`.

Then integration:
```
hbridge
  → qVFamNormRatio_ge_one (Generic, currently conditional on hbridge)
  → RouteA.finalPaperNormalizedComparison_noS45_of_ratio_ge_one
  → finalPaperNormalizedComparison_noS45
```

Pitfalls to expect:
- Do not try to state both norms on the same type via typeclass inference; use
  `toC`/`C place` for the default formula and `L place` for the donor formula, then
  only compare the resulting real numbers.
- `norm_eq_absNorm_zpow` needs the nonzero hypothesis for `toC x`;
  `simpa [toC]` from `hx`.
- `Real.rpow_mul` requires base positivity; use the donor's `absNorm_pos`.
- `qVFamDefaultNorm` and `qVFamNormalizedNorm` unfold to the same underlying
  element; `simpa [qVFamDefaultNorm, qVFamNormalizedNorm, qVFamNormalizedGenerator,
  GeneralNormalizedNormBySpectralUniqueness.toC]`.

No Lean changes made; this is the exact hbridge proof route.

## hbridge current implementation status (2026-11-14 15:30, read-only)

Two candidate hbridge files exist, both currently red:

### `Mzk1P0QVFamNormBridgeDonorActual.lean` (no olean; latest FAIL 15:30)
Contains the intended unconditional
`qVFamNormalizedNorm_eq_defaultNorm_rpow` and `qVFamNormRatio_ge_one`, but:
- `:67:8` `generalNormalizedNormFormula` argument type mismatch: the donor lemma is
  stated for `x : NormalizedCompletion place`, while `qVFamNormalizedGenerator` has
  the reducible `CommonPrimeCompletion` spelling; the expected/actual `Zero` instances
  differ syntactically.  Fix: pass an explicit
  `(show NormalizedCompletion (qVFamTensorPlace T b) from qVFamNormalizedGenerator T b)`
  or `change`/`simpa [CommonPrimeCompletion, NormalizedCompletion]` before applying the
  donor lemma (the BridgeValue file already uses this explicit `show` pattern).
- `:77:51` `WithZero.unzero hv`: implicit value inferred from a different
  `Valued.v` instance.  Fix: state `hv` at the explicit
  `NormalizedCompletion`/`toC` carrier (as BridgeValue does), or give
  `WithZero.unzero (a := Valued.v (toC ...)) hv`.
- `:138` final paper comparison needs `[Fintype (Bad (nativePlaceSelection T))]`;
  add the instance variable before that theorem (the pairwise ratio lemma does not
  need it).  The later `unknown identifier T` errors are cascades from this.

### `Mzk1QVFamNormBridgeValueActual.lean` (no olean; latest FAIL 15:23)
Tries the cleaner value-level proof:
- `:41` normalized formula `simpa` type mismatch — same
  `CommonPrimeCompletion` vs `NormalizedCompletion` instance issue.
- `:70/:71` rewrite default formula pattern not found, `:75/:76` unsolved goals —
  the `change` to the default norm is not in the same `Valued` instance expected by
  `norm_eq_absNorm_zpow`; use the explicit `toC` carrier and
  `show NormalizedCompletion ... from (qVFamily T b).q` as already attempted in
  `qVFamDefaultNorm_eq_absNorm_rpow`, then `simpa [toC]` rather than `rw`.

**Exact repair order:**
1. Put the qVFamily element under the explicit `NormalizedCompletion` carrier
   everywhere the donor is called.
2. State the default formula on `toC x : C place`, not on the L carrier; use
   `valuation_ne_zero_of_ne_zero` and the explicit `WithZero.unzero` value.
3. Derive `qVFamDefaultNorm = absNorm^m` by `simpa [qVFamDefaultNorm, toC]`.
4. Use `Real.rpow_mul` with `absNorm_pos`.
5. Add `[Fintype (Bad ...)]` for the final global comparison only.

No Lean changes made; the hbridge route is otherwise exactly as described above.

## hbridge latest status (2026-11-14 15:40, read-only)

`Mzk1P0QVFamNormBridgeDonorActual` has been edited since the previous check and is
close: the latest run's remaining errors are

- `:84:51` `WithZero.unzero hv` / `WithZero.unzero (show val ≠ 0 from hv)`:
  the implicit `x` argument of `WithZero.unzero` is not inferred from the local
  `let val := Valued.v (toC ...)`; elaboration expects `?m ≠ 0`.  Give the implicit
  explicitly, e.g.
  `WithZero.unzero (x := val) hv` (or restate `hv` for the exact
  `WithZero` value term appearing in `WithZero.log val`).
- `:150:2` `Unknown identifier exact` in
  `finalPaperNormalizedComparison_noS45`: the theorem body starts with
  `:= have h ...; exact ...` and is missing `by` (term/tactic mode mismatch).
  Add `:= by` before the `have`, or use the direct term
  `finalPaperNormalizedComparison_noS45_of_ratio_ge_one T (fun b => qVFamNormRatio_ge_one T b)`.

Earlier errors (donor argument type, missing imports, Fintype) no longer appear in
the latest tail; Generic conditional and RouteA remain green.  Once the two fixes above
land, BridgeDonor should produce the unconditional
`qVFamNormalizedNorm_eq_defaultNorm_rpow` and `qVFamNormRatio_ge_one` and the final
S45-free wrapper can be imported.

No Lean changes made.

## hbridge latest error interpretation (2026-11-14 15:52, read-only)

The latest BridgeDonor run has narrowed further; the remaining errors are now
**elaboration/coercion**, not mathematical:

- `:84:34`, `:90:30`, `:104:33`, `:110:32`:
  `WithZero.unzero hv` returns `Multiplicative ℤ`, but the surrounding
  `Multiplicative.toAdd ... : ℝ` makes Lean infer the target
  `Multiplicative ℝ` (because `toAdd`'s implicit `α` is inferred from the expected
  real type).  Fix by fixing the value-group parameter explicitly:
  `Multiplicative.toAdd (α := ℤ) (WithZero.unzero (x := val) hv)`, then
  `((... : ℤ) : ℝ)`, or define `m : ℤ := Multiplicative.toAdd ...` first and cast
  `(m : ℝ)`; do not put the `: ℝ` coercion directly around the `toAdd` term.
- `:85:73` unsolved `ring` goal: same `unzero/toAdd` type issue in `hm`; after
  fixing the ℤ annotation, the `rw [hnu]; ring` step should close.
- `:97:4` `simpa only [...] using hnorm` type mismatch: both sides print the same
  `absNorm^...` term, but the norm instance/coercion is not definitionally identical
  under `simpa only`.  Use a `change` to the literal
  `‖qVFamNormalizedGenerator T b‖ = ...` shape before `exact hnorm`, or use
  `convert hnorm using 2` and close the instance goal by `rfl`.

So the hbridge proof route itself is correct; the remaining work is:
1. bind `m := Multiplicative.toAdd (α := ℤ) (WithZero.unzero (x := val) hv)` and use
   `(m : ℝ)` in `hm`/`hdef'`/calc;
2. use `change`/`convert` for `hnorm'` instead of `simpa only`;
3. final theorem body needs `:= by` (or direct term) as noted earlier.

No Lean changes made.

## Integration check after donor GREEN (2026-11-14 17:20, read-only)

**Donor is now GREEN:** `Mzk1P0QVFamNormBridgeDonorActual.olean` (17:15:33,
watchdog DONE 17:15:34).  It contains the unconditional
`qVFamNormalizedNorm_eq_defaultNorm_rpow`, `qVFamNormRatio_ge_one`, and
`finalPaperNormalizedComparison_noS45`.

Downstream status:

- `Mzk1RouteAFinalNoS45WrapperActual`: GREEN (15:13:52); still useful as the
  generic wrapper, but the donor now gives the final comparison directly.
- `Mzk1P0FinalS3137ConditionalActual`: source 17:20:18 is newer than its olean
  (15:54:14); watchdog START 17:21 is rebuilding it.  Current source already imports
  `Mzk1P0QVFamNormBridgeDonorActual` and defines the **unconditional**
  `finalPaperNormalizedComparison : paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T`
  using `Mzk1P0QVFamNormBridgeDonorActual.finalPaperNormalizedComparison_noS45`.
  It also keeps the conditional `..._ofNormBridge` wrapper and the S45-strict
  `finalPaperNormalizedComparison_strict`.
- `Mzk1P0FinalS3137DictionaryActual`: source 16:10:40, olean 16:14:21.  Its
  `finalDictionaryCombined` **still takes `S : S45SourceFields`** and proves the
  comparison via `paperNormalizedComparison_of_sourceFields`; it has only a
  conditional `finalDictionaryCombined_ofNormBridge`.  It has **not yet been updated**
  to use the unconditional donor comparison.
- `Mzk1P0FinalS3137AxiomProbeActual`: still probes the conditional
  `finalPaperNormalizedComparison_noS45_ofNormBridge`, not the new unconditional
  `finalPaperNormalizedComparison`/`finalDictionaryCombined_noS45`.

Exact remaining integration work (source edits, not done here):

1. In `Mzk1P0FinalS3137DictionaryActual`, add the S45-free combined theorem
   `finalDictionaryCombined_noS45 (rel) (lock)` whose first conjunct is
   `Mzk1P0FinalS3137ConditionalActual.finalPaperNormalizedComparison` (or directly
   `Mzk1P0QVFamNormBridgeDonorActual.finalPaperNormalizedComparison_noS45 T`),
   keeping `rel` and `lock`.  Drop `S` from this new theorem; leave the old
   S45 version for compatibility/strict use.
2. Retouch/rebuild `Mzk1P0FinalS3137DictionaryActual` after that source edit; its
   current olean predates the donor GREEN and the new unconditional path.
3. Retarget `Mzk1P0FinalS3137AxiomProbeActual` to
   `finalPaperNormalizedComparison` and `finalDictionaryCombined_noS45`, then retouch
   to get fresh axioms after the dictionary rebuild.
4. Optionally drop `s45` from `FinalBridgeConditions`/`finalBridgeConditions_of` for
   the paper-comparison part; keep the structure field only if a consumer still needs
   the original S45 source condition.
5. Rebuild `Mzk1P0FinalS3137ConditionalActual` (currently in progress) and verify its
   new olean is later than the donor; then verify final dependency freshness.

No Lean changes made; this is the exact integration/dependency state.
