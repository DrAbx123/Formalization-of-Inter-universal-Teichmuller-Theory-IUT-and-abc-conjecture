# S45 `qVFamNormRatio = 1` under the donor power formula

Date: 2026-11-14. Lane: stage4. **Read-only note; no Lean file was modified or added.**

## Inputs (all green)

- Donor `LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean`:
  `generalNormalizedNormFormula (x) (hx : x ≠ 0) :
  ‖x‖ = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ))`
  where `L place := NormalizedCompletion place`, `nu x = -log (Valued.v x)`,
  `d place = relativeCompletionDegree (k := ℚ) place`; olean present, watchdog DONE.
- Default norm formula `FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow`:
  for `x ≠ 0` in the default `Completion place`, `‖x‖ = absNorm ^ m` with
  `m = log (Valued.v x) = -nu x`.
- `QVFamNormalizedCoefficientBridgeActual`:
  `qVFamNormalizedNorm = ‖qVFamNormalizedGenerator‖` (normalized/spectral),
  `qVFamDefaultNorm = ‖(qVFamily q).q‖` (default),
  `qVFamNormRatio = qVFamNormalizedNorm / qVFamDefaultNorm`,
  `qVFamNormalizedCoefficient = -logb_p qVFamNormalizedNorm`,
  and `qVFamPureCoefficient = -logb_p qVFamDefaultNorm`.
- S45 fields: `BadPlaceNormalizedSourceHypothesisActual.NormalizedSourceHypothesis`:
  `∀ b, qVFamNormRatio b = 1 ∧ log(residueNormBase place_b) = log p_b`.

## Exact power computation

Let `place = qVFamTensorPlace T b`, `p = qVFamTensorP T b`, `r = ‖q‖_default < 1`
(q is a nonunit, so `r < 1`), and `d = [K_place : Q_p] = relativeCompletionDegree (k:=ℚ) place`.
Then for `x = q` (`x ≠ 0`), with `ν = -log r > 0`:

```
default norm:      r = absNorm^(-ν)
normalized norm:   ‖q‖_norm = absNorm^(-ν/d) = r^(1/d)
qVFamNormRatio = ‖q‖_norm / r = r^(1/d - 1) = r^((1-d)/d)
log(qVFamNormRatio) = (1/d - 1) * log r = ((1-d)/d) * log r.
```

Because `0 < r < 1` (`log r < 0`):

- if `d = 1`, then `qVFamNormRatio = 1`;
- if `d > 1`, then `(1/d - 1) < 0`, so `qVFamNormRatio > 1`; hence
  **S45's first condition `qVFamNormRatio = 1` is FALSE for d > 1**;
- more generally (with `q` nonunit), `qVFamNormRatio = 1 ↔ d = 1`.

The donor power formula therefore does **not** imply S45; it implies the exact
correction factor `r^(1/d - 1)` for `d > 1`, and S45 is equivalent to the local
degree-one case (for the nonunit q).

## Which norm does the paper normalization use?

The paper-normalized coefficient in
`BadPlacePaperNormalizedComparisonActual.paperNormalizedCoefficient`:
```
paperNormalizedCoefficient = order * log(residueNormBase place_b) / log p_b
```
is the **default valuation-norm coefficient**; it coincides with
`qVFamPureCoefficient = -logb_p ‖q‖_default`.  The tensor constructor instead needs a
generator in `CommonPrimeCompletion` with the **normalized spectral norm**, and the
green bridge proves
```
qVFamNormalizedCoefficient = paperNormalizedCoefficient
    - log(qVFamNormRatio) / log p_b.
```
So the paper normalization is the default/valuation norm; the normalized spectral
norm is the bridge used by the tensor constructor.  S45 is exactly the assumption
that this bridge is the identity (`qVFamNormRatio = 1`), not a consequence of the
paper normalization.  This matches
`Mzk1P1NormalizedSourceConditionalActual`'s description of S45 as the
paper correction-free normalized-source hypothesis.

## Can `d > 1` be derived from local degrees?

No, not in the current tree.  The available unconditional facts are only:

- `0 < relativeCompletionDegree (k := ℚ) place` (positivity), hence `1 ≤ d`;
- `0 < qVFamTensorRationalDegree` (residue degree), and `d = e * f`
  (`relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg`), hence `d ≥ f`;
- no theorem establishes `1 < d`, `1 < e`, or `1 < f` for the qVFamily F-place.

In particular, `localCompletionDegree (nativeBadToKPlace b) = [K_w : (F_mod)_v]`
is a **different** local degree (K over F_mod) and does not identify `d` for the
F-place; it cannot be used to prove `d > 1` for `qVFamTensorPlace`.

Consequently the honest statement is conditional:
```
1 < d  →  qVFamNormRatio ≠ 1   (q nonunit),
qVFamNormRatio = 1  →  d = 1.
```
S45 as a theorem is false at every `d > 1` place; whether such a place exists in a
given source datum is not decided by the local-degree data currently formalized.

## Bottom line

- Paper normalization = default valuation norm; normalized spectral norm is the
  tensor-side bridge.
- Donor gives normalized = default^(1/d); consequently S45 `qVFamNormRatio = 1` is
  false for `d > 1` (nonunit q), with exact ratio `r^(1/d - 1) > 1`.
- `d > 1` cannot be derived from current local-degree facts; S45 must stay an
  explicit condition, equivalent (for nonunit q) to the local degree-one case.

No Lean changes made.
