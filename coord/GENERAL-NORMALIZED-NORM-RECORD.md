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

## Verified evidence (watchdog only)

- Donor `GeneralNormalizedNormBySpectralUniqueness`: DONE EXIT=0 2026-11-14T06:04:03Z (55s), olean 586400B @14:04:02+08.
- Donor axiom probe `tmp/sheaf/xif/paper/Mzk1GeneralNormalizedNormAxiomProbeActual.lean`: DONE 06:04:01; `generalNormalizedNormFormula`, `normalizedCanonicalPowerComparison`, `canonicalAbsValue_extends` each depend only on `[propext, Classical.choice, Quot.sound]`.
- Downstream `CanonicalAbsValueAddLeProof`: DONE EXIT=0 2026-11-14T06:12:20Z (50s), olean present; proves `canonicalAbsValue_add_le` max form; donor does not import it (no cycle).
- Composite `Mzk1IUTIVProp11CompositeActual`: DONE 06:06:46Z; probe `Mzk1IUTIVProp11CompositeAxiomProbeActual`: DONE 06:17:01Z, `iutIVProp11_tensorPacket_composite` only `[propext, Classical.choice, Quot.sound]`.
- LS3137: `Mzk1P0LS3137LFinalActual` DONE 05:57:00Z (imports/opens replicated from `Mzk1S3137LReadoutActual`).

## Explicitly EXCLUDED residual files (stale old all-x API)

The following files are NOT in the watchdog worklist, have NO olean, and are NOT counted as verified:

- `GeneralNormalizedNormFinal.lean` (imports the old all-x donor API and `NormalizedNormSpectralBridge`)
- `GeneralNormalizedNormConsumer.lean` (re-exports the old chain)
- `NormalizedNormSpectralBridge.lean` (calls nonexistent donor name `spectralNorm_eq_formula` and old all-x formula)
- `GeneralNormalizedNormFinalWiringFixed.lean` (imports the consumer/Final chain and `GeneralNormalizedNormFormula`)

Reason: they were written against the unverified old all-x statement and a nonexistent donor name; they predate the
verified restricted statement `generalNormalizedNormFormula (x) (hx : x ≠ 0)` and the normalized carrier `L := NormalizedCompletion place`.
To bring any of them back into the build: replace the all-x uses by the `(x) (hx)` version, fix `spectralNorm_eq_formula` to
`canonicalAbsValue_eq_spectralNorm` / `normalizedNorm_eq_spectralNorm`, and re-add only after they compile under the watchdog.

## S45 realization route (analysis; no overclaim)

- `qVFamNormRatio T b = qVFamNormalizedNorm T b / qVFamDefaultNorm T b` where
  `qVFamNormalizedNorm = ‖qVFamNormalizedGenerator T b‖` (normalized/spectral norm) and
  `qVFamDefaultNorm = ‖(qVFamily T b).q‖` (default/valued-adic norm).
- Donor gives, on the normalized carrier and for `x ≠ 0`: `‖x‖ = absNorm^(-ν(x)/d)`; on the raw adic completion the ambient norm is the
  canonical valued-adic norm `absNorm^(-ν(x))`. Hence, under an explicit carrier-identification hypothesis, the ratio would be
  `absNorm^(-ν/d + ν) = absNorm^(ν(1-1/d))`, which equals 1 only when `ν = 0` (unit) or `d = 1`; for `d > 1` and `ν ≠ 0` it is ≠ 1.
- Therefore **S45 `qVFamNormRatio = 1` is a genuine extra condition, NOT implied by the donor power formula**; it must stay explicit
  (it is exactly the paper normalized-source hypothesis). The donor cannot close `CommonPrimeNormInstanceCompat` either (that asks
  norm equality across presentations, which the power formula does not give unless d = 1).
- Concrete next construction (honest): keep `QVFamNormInstanceGap := qVFamNormalizedNorm = qVFamDefaultNorm` as the explicit lock;
  prove the iff `qVFamNormRatio = 1 ↔ QVFamNormInstanceGap` (needs nonzero default norm) and, if desired, a conditional power-ratio
  formula under an explicitly named carrier-identification hypothesis (never assumed as true).

## Tower correction (2026-11-14, lead/user)

- `rootBaseQpDegree = [F_v : Q_p]`; `localCompletionDegree = [K_w : (F_mod)_v]`; `kPlaceQpDegree = [K_w : Q_p]`.
  The F-place and K-place share only the `F_mod`-place; the tower is
  `dBase = [(F_mod)_v : Q_p]`, `e = [F_v : (F_mod)_v]`, `n = [K_w : (F_mod)_v]`, with
  `rootBase = e * dBase` and `kPlace = n * dBase`.  Do NOT use `dL = B*n` or
  `dK = n*rootBaseQpDegree`.

## R3 / sign correction (2026-11-14, lead/user)

- Cor 3.12 uses `-|log Θ|` as NOTATION for the signed log-volume (the proof handles the
  nonnegative case separately); do not treat it as globally nonpositive and do not add an
  extra negative sign between signed readings.
- R3 should compare region mass RELATIVE to the reference lattice via
  `NormalizedHaarTransport.relative_log_mass_image_eq` (NormalizedHaarTransport.lean:39),
  which cancels the Haar scalar; for different-dimensional root/completion data compare
  extended ideals and dimension-normalized volume, not the target Haar on a low-dim image.
  This replaces the raw-Haar calibration `raw = d·normalized + log μ(R)` as the primary R3 route.

## N5 / StepV-floor q-pilot source (2026-11-14)

- Native N5 green: `Mzk1IVThm110N5Actual`: `S3013MagnitudeNonnegTarget_actual`,
  `native_qSideSignedValueCondition_actual`, `actualS3013QSource` (from
  `PaperXiFGlobalDirectActual.nativeGlobalQPilotNormalizedLogMagnitude_nonneg`).
- Floor transfer green: `Mzk1IVThm110N5FloorBridgeActual` (20:26:21), conditional on
  `FloorNativeQBridge : floorQSigned = S3013QSigned` (and htheta/hCTheta explicit).
- Shared R1/N5 witness (EXPLICIT GAP): `S3013QPilot T = P.line.C3.q.q = qVFamNormalizedGenerator T b`
  plus Bad-place/index/weight transport.

## Shared q-pilot scalar: exact missing identifications (2026-11-14)

Green anchors: `S3013QSigned T = -nativeGlobalQPilotNormalizedLogMagnitude T` (N5 native),
`P.signedQPilotLogVolume = Real.log ‖P.line.C3.q.q‖` (rfl), `M = Σ w_b baseQLogMagnitude b`.

Missing (no repo bridge):
1. C3/native: `Real.log ‖P.line.C3.q.q‖ = -M` (R1 scalar).
2. qVFam/native: `actualQPilotMagnitudeClassical T = M` (per-b `c_norm*log p = baseQLogMagnitude`, same weights).
3. floor/native: `min(arithmeticTupleCanonicalHullHaarLog places tuple μ, -1) = -M` (qpilot FloorNativeQBridge).

Type caveat: `P.line.C3.q.q : Completion place` (canonical) vs `qVFamNormalizedGenerator : CommonPrimeCompletion`
(normalized) are not defeq; relation is `‖·‖_norm = ‖·‖_def^(1/d_F)` (power). No element equality claim.

## Exact qVFam-vs-native magnitude difference (2026-11-14)

- `actualQPilotMagnitudeClassical = Σ W_b c_norm_b log p_b` (qVFam normalized coefficient, place `qVFamTensorPlace`).
- `M = nativeGlobalQPilotNormalizedLogMagnitude = Σ W_b baseQLogMagnitude_b`,
  `baseQLogMagnitude_b = -log‖(baseQ T b).q‖` (baseQ at `nativeBaseSectionPlace`).
- Different q and place; `actualQ = M` is NOT assumed and is false in general.
- Under same-q identification (`qVFamDefaultNorm b = ‖(baseQ)b.q‖`), donor power gives
  `c_norm*log p = baseQLogMagnitude/d_b`, hence `actualQ ≤ M` (strict for d>1, baseQ>0).
  Direction: `-M ≤ -actualQ = actualQPilotSignedLogClassical`; therefore if
  `P.signedQPilotLogVolume = -M` (C3 readout identity, currently unproved) then R1 holds
  without equality and without normRatio=1.

## Place/element type facts for same-q (2026-11-14)

- `qVFamTensorPlace T b : FinitePlace T.arithmetic.F` (F-side, `(nativeBadLift T).lift b`);
- `nativeBaseSectionPlace T b : FinitePlace T.arithmetic.K` (K-side, sectionFiniteLift);
  both contract to `b.1`, but F ≠ K ⇒ place equality type-incorrect.
- `(qVFamily T b).q : Completion (qVFamTensorPlace)` (F) vs `(nativeBaseQFamily T b).q : Completion (nativeBaseSectionPlace)` (K)
  ⇒ element equality type-incorrect; missing theorem = base-change place/completion correspondence + element correspondence.
- `P.signedQPilotLogVolume = log‖P.line.C3.q.q‖` is a single local log, while `M = Σ_b W_b baseQLogMagnitude_b`;
  equality `P.signed = -M` needs P.line.C3↔baseQFamily place/element identification AND an aggregate/index-weight argument,
  otherwise the comparison must be per-b + weighted.

## Base-change correspondence structures (2026-11-14)

- `Mzk1BaseChangeQCorrespondenceActual` green (structures, no inhabitant):
  `BaseChangePlaceCompletionCorrespondence` (fPlace/kPlace/comap_F/lift/comaps/completionMap/n+norm power),
  `BaseChangeQElementCorrespondence`, `QPilotC3SignedAggregation`, conditional R1 theorem.
- Reusable actual map: `FinitePlaceExtension.completionMap (k := F) (K := K) kPlace`
  : `(comap_F kPlace).adicCompletion F →+* kPlace.adicCompletion K` (green, injective; valuation lemmas).
- Norm scaling is a POWER: `‖completionMap x‖ = ‖x‖^n`, n = [K_w:F_v] (NOT preservation).
- First exact gaps: (a) `comap_F (nativeBaseSectionPlace T b) = (nativeBadLift T).lift b`;
  (b) norm power formula for completionMap; (c) element correspondence qVFamily ↔ nativeBaseQFamily;
  (d) C3 signed = -M aggregation.

## (c)(d) three carriers (2026-11-15)

- `qVFamily T b` : F-level, `Completion ((nativeBadLift T).lift b)`; source = clauseB comparison parameter.
- `nativeBaseQFamily T b` : K-level, `Completion (nativeBaseSectionPlace T b)`; source = badPlaceQCandidate.
- `P.line.C3.q` : Fmod-level, `Completion (C3.place.val)` with `C3.place : FinitePlaceAtPrime Fmod p`;
  `P.signedQPilotLogVolume = Real.log ‖C3.q.q‖`.
- (c) missing: completionMap(qV q) = baseQ q — clauseB parameter vs native DVR candidate identification (not implied by hplace).
- (d1) missing: C3.place.val = b.1 and same Fmod-level q; norm scales: baseQLogMagnitude = n * (-log‖C3.q.q‖);
  (d2) missing: single place / global weighted sum collapse `M = W_b * baseQLogMagnitude_b`.
