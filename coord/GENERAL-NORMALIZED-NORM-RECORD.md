# General normalized norm (donor) — verified record

File: `LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean`
Status: GREEN (watchdog DONE 2026-11-14T05:58:55Z, 54s; olean present, source newer check done).
No `sorry`/`axiom`/`True` in source.

## Corrected statements (must be quoted with the x≠0 restriction)

- `canonicalAbsValue_extends (q : K place) : canonicalAbsValue place (algebraMap (K place) (L place) q) = ‖q‖`
- `canonicalAbsValue_eq_spectralNorm (x : L place) : canonicalAbsValue place x = spectralNorm (K place) (L place) x`
- `generalNormalizedNormFormula (x : L place) (hx : x ≠ 0) : ‖x‖ = (absNorm place) ^ (-(nu place x : ℝ) / (d place : ℝ))`
- `normalizedCanonicalPowerComparison (x : L place) (hx : x ≠ 0) : ‖x‖ ^ (d place) = ((absNorm place) ^ nu place x)⁻¹`
- `nu_add_ge_min (x y : L place) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0)`
- carrier: `L place := NumberFieldFinitePlace.NormalizedCompletion place`; `C place := place.maximalIdeal.adicCompletion F` only internal (`toC`, `nu`); `K place := PadicScalarField place`.

## Corrections (evidence, no overclaim)

1. The all-x formula is FALSE under project definitions: `WithZero.log_zero` ⇒ `nu 0 = 0` ⇒ RHS `absNorm^0 = 1`, while `‖(0:L)‖ = 0`. The verified statement is restricted to `x ≠ 0`. This matches the project-only `GeneralNormalizedNormFormula (x) (hx)` formulation.
2. In this Mathlib `AbsoluteValue.add_le'` is the ARCHIMEDEAN inequality `f (x+y) ≤ f x + f y` (not `max`). The verified `AbsoluteValue` uses `canonicalFun_add_le_sum`; the nonarchimedean max bound `canonicalFun_add_le` (restricted x,y,x+y≠0) is proved separately. The old `CanonicalAbsValueAddLeProof` max-goal target was not the required field and the file had never compiled.
3. Ambient `‖·‖` on `place.maximalIdeal.adicCompletion` is the canonical valued-adic norm, while `absNorm^(-nu/d)` is the NORMALIZED (spectral) norm; they differ when `d ≠ 1`. Hence the donor uses `L place := NormalizedCompletion place`. It gives a POWER relation `‖x‖_norm = absNorm^(-ν/d) = ‖x‖_def^(1/d)` (x≠0), NOT norm equality.
4. Consequence: this donor does NOT imply S45 `qVFamNormRatio = 1` and must not be used to close `CommonPrimeNormInstanceCompat`; S45 stays an explicit condition.
5. Misc: `d = e*f` is rfl; `relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg` unnecessary; `Real.rpow_le_rpow_left₀` absent (honest lemma `Real.rpow_le_rpow_of_exponent_le`).
