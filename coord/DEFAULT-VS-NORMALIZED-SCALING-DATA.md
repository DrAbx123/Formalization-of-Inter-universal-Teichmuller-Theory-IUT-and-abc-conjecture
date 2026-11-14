# Default-norm vs normalized `ArithmeticTuplePureFractionalScalingData`

Date: 2026-11-14. Lane: stage4. **Read-only analysis; no Lean file was modified or added.**

## Question

Can `ArithmeticTuplePureFractionalScalingData` be built from a **default Completion**
generator q (norm `p^(-paperCoeff)`) instead of the normalized spectral supply, and does
that remove S45?  Is a default-norm variant compatible with downstream consumers
(`FinitePlaceStepVAssembly` / S3137), or should the paper object be normalized?

## Exact structure requirement

`FinitePlaceNormalizedUnitScalingLogVolume.ArithmeticTuplePureFractionalScalingData`
(lines 133-153) has
```
localGenerator : (i : ι) → CommonPrimeCompletion (places i (tuple i))
localGenerator_norm : ∀ i, ‖localGenerator i‖ = (p : ℝ) ^ (-(c i))
localUnit : (i : ι) → CommonPrimeCompletion (...), ‖localUnit i‖ = 1
localGenerator_pow : localGenerator i ^ commonExponent = p^(integerExponent i) * localUnit i
unitTensor_action / integerTensor_mul_holomorphic ...
```
and `FinitePlaceStepVAssembly.arithmeticTuplePureFractionalScalingData_ofGenerator`
(lines 112-...) only accepts generators in `CommonPrimeCompletion` with normalized norm
`‖g i‖ = p^(-(c i))`.  There is no default-norm field and no alternative constructor in
the current production API.

## Downstream consumers are normalized

- `FinitePlaceNormalizedUnitScalingLogVolume`: all counting/Haar volume theorems are for
  `ArithmeticTensorTupleBlock places tuple`, whose local factors are exactly
  `CommonPrimeCompletion`; scaling and norm-power lemmas use the normalized norm of
  `localGenerator`.
- `FinitePlaceStepVAssembly` lines 173-186 and 496-551:
  `arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator`,
  `arithmeticTupleNormalizedLogVolume_stepVEndpoint`, and the StepV paper bound all
  take/construct the data through `CommonPrimeCompletion` and the normalized Haar volume.
- `Mzk1StepVScalingDataActual.stepVScalingDataOfGenerator` and
  `stepVRegion_volume_eq_ofGenerator` take generators in `CommonPrimeCompletion`;
  `S3137FinalResidualManifestActual` records the missing R2 object literally as
  `Nonempty (ArithmeticTuplePureFractionalScalingData ... rootHalfCoefficient)` with
  normalized Q_p-spectral coefficient (`c_norm = order/e`, not the default-residue
  `order/(2l)`).

**Compatibility verdict:** a default-norm variant is **not drop-in compatible**.  It would
require a parallel tensor block/measure API over `Completion` (the default valuation norm)
and re-proving the norm-power/p^{-c} Haar scaling lemmas there; the existing consumers all
expect `CommonPrimeCompletion` and the normalized spectral norm.  Transporting a default
norm to the normalized tensor block is exactly the norm-instance comparison that needs S45
(or the power formula), so a default-norm variant does not remove that work.

## Paper object should be normalized

The paper-normalized coefficient is a **default-norm number**:
`paperNormalizedCoefficient = order * log(residueNormBase)/log p`, equal to
`-logb_p ‖q‖_default`.  The object fed to the tensor/StepV machinery, however, must be a
normalized `CommonPrimeCompletion` generator.  The correct object is therefore normalized;
the default coefficient is represented by a normalized generator with the same
`p`-power norm, not by replacing the tensor block carrier with the default norm.

## S45-free construction at the paper coefficient (exact route)

Let `d = relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b)` and
`q_norm := qVFamNormalizedGenerator T b` (the actual q in `CommonPrimeCompletion`).  The
green donor gives, for `x ≠ 0`,
```
‖x‖_norm = absNorm^(-ν(x)/d) = ‖x‖_default^(1/d),
```
so with `r = ‖q‖_default < 1` and `paper = -logb_p r` (`= paperNormalizedCoefficient`):
```
‖q_norm‖ = r^(1/d) = p^(-paper/d),
‖q_norm ^ d‖ = ‖q_norm‖^d = r = p^(-paper).
```
The element `g := q_norm ^ d` is nonzero and lives in `CommonPrimeCompletion`, so
`arithmeticTuplePureFractionalScalingData_ofGenerator` can be applied at the coefficient
family `paperCoeffFamily` (constant per b) using `(fun _ => g)` and the norm identity
`‖g‖ = p^(-paper)`.  This builds the paper-coefficient scaling data **without S45**
(it only uses the donor power formula and `norm_pow`), and it is fully compatible with the
normalized downstream API.

**Caveat (important):** `g = q_norm^d` is the normalized representative of q's
**default-norm coefficient**; it is not the element q in the normalized completion.  If a
consumer needs the actual q's normalized scaling (coefficient `c_norm = paper/d`), keep the
existing `qVFamNormalizedPureFractionalScalingData` at `c_norm` and the explicit
`log(qVFamNormRatio)` correction.  The two data objects are different: one encodes the
paper/default coefficient, the other the actual normalized q.  This construction removes
S45 from the scaling-data existence step, but not from any statement that explicitly
identifies the actual q's normalized norm with its default norm.

## S3137 compatibility

S3137's R2 residual is a **normalized 2l-th root supply**
(`ArithmeticTuplePureFractionalScalingData ... rootHalfCoefficient`); the qVFamily
`q_norm^d` construction is a different coefficient/object and does not fill R2.  R2 should
stay normalized and explicit; do not switch it to a default-norm variant.

## Bottom line

- A default-norm `ArithmeticTuplePureFractionalScalingData` variant is **not compatible**
  with `FinitePlaceStepVAssembly`/S3137; the paper object should be **normalized**.
- S45 can be bypassed for the qVFamily **paper-coefficient scaling data** by using the
  normalized generator `q_norm^d`, whose norm is `p^(-paper)` by the donor power formula.
- This does not remove S45 from statements comparing actual q's normalized vs default
  norms, and does not fill S3137 R2's normalized root supply.

No Lean changes made.
