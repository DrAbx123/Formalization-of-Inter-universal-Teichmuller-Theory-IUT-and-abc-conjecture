# Norm-instance gap: default Completion norm vs NormalizedCompletion spectral norm

Date: 2026-11-14. Lane: stage4. **Read-only note; no Lean file was modified or added.**

## Objects and proved facts

`NormalizedCompletion place := Completion place` (same underlying type;
`normalizedCompletionRingEquiv` is `RingEquiv.refl`, but the `Norm` instances differ).

| Fact | File / theorem | Status |
|---|---|---|
| Normalized norm is the spectral Qp-norm | `Example36CompletionIsometry.normalizedCompletion_norm_eq_spectralNorm` | green |
| Identity map is a homeomorphism, not an isometry | `FinitePlaceNormalizedCompletion.normalizedCompletionHomeomorph` | green |
| The two norms have the same closed unit ball | `FinitePlaceNormalizedIntegers.normalizedCompletion_norm_le_one_iff` | green |
| The two norms have the same open unit ball | `FinitePlaceNormalizedIntegers.normalizedCompletion_norm_lt_one_iff` | green |
| Default completion norm formula | `FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow`, `logNorm_eq_absNorm_mul` | green |
| Exact norm ratio / gap Props for qVFamily | `QVFamNormalizedCoefficientBridgeActual.qVFamNormRatio`, `QVFamNormInstanceGap`, `QVFamNormalizedCoefficientGap` | green (Props, not asserted) |

Only unit-ball/topology agreement is proved in the tree.  No theorem states the
*numerical* equality `||x||_normalized = ||x||_default` for nonzero `x`.

## Exact missing analytic input

`Example36CompletionNormFormula` records the missing statement as
`NormValuationCompatible place e_w` (and its equivalent p-power/spectral spellings):
```
log ||x||_normalized = - (completionValuationExponent x / e_w) * log p,
equivalently ||x||_normalized = p ^ (-(nu x / e_w))
```
for units `x` of the normalized completion, with `e_w` the relative ramification
index over Q.  The file explicitly says this formula is **NOT proved** in the tree;
all deductions from it are conditional.  The default norm is known exactly:
`log ||x||_default = m * log absNorm`, where `m` is the discrete valuation exponent
and `absNorm = p ^ f_w`.

Consequently, on the same element `x != 0`:
```
log ||x||_default   = - f_w * nu * log p
log ||x||_normalized = - (1/e_w) * nu * log p        (missing NormValuationCompatible)
```
so the expected relation is
```
||x||_normalized = ||x||_default ^ (1 / (e_w * f_w)) = ||x||_default ^ (1 / d_w),
d_w = [K_w : Q_p].
```
This is exactly the object-level norm-instance conversion; it is **not currently
available** and must not be asserted.

## Consequences for the qVFamily gap

Let `d = [K_v : Q_p]` for the actual completion place and let `r = ||q||_default < 1`.
Under the missing formula:
```
qVFamNormRatio = ||q||_normalized / ||q||_default = r ^ (1/d - 1) > 1   (if d > 1),
QVFamNormInstanceGap  <=>  qVFamNormRatio = 1  <=>  d = 1   (since r != 1).
```
Thus the norm-instance gap is **not a counterexample obstruction but an open
dichotomy**: it closes exactly in the degree-one (unramified degree-one) local case;
for `d > 1` the two norms genuinely differ and the correction is the exact power
`r^(1/d - 1)` (assuming the missing formula).

Candidate route to prove it (not currently built):
`GeneralNormalizedNormBySpectralUniqueness.generalNormalizedNormFormula` and
`normalizedCanonicalPowerComparison` in
`LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean`
claim the formula via `spectralNorm_unique_field_norm_ext`.  That file currently has
**no olean and is not in the watchdog target list**, so it is an unverified donor,
not a green theorem; it must be built/audited before use.

## Reuse consequences for A1/L readouts

- A1 signed readout stays in **measure/norm-ball** form and never needs the norm
  equality; this is why it can ignore the gap.
- `QhatHaarScalingReuse` uses the root-extension Haar factor, not the default/normalized
  q norm equality; also independent of the gap.
- L-side paper-q norm correction `qhatLogReadout - paperQSignedReadout = log(qVFamNormRatio)`
  keeps the gap explicit as a conditional/ratio, which is the correct treatment while
  `NormValuationCompatible` is unproved.
- Do not replace `qVFamNormRatio` by 1 in any consumer unless the local degree-one
  case is separately established.

## Bottom line

Exact obstruction: the tree proves only unit-ball/topology equality between the default
`Completion` norm and the normalized spectral norm; the numerical relation is the frozen
input `NormValuationCompatible` (normalized = default^(1/d_w)).  No fake equality.  Route
to close is the general normalized norm formula via spectral uniqueness, which exists as
source but is not a built/verified target in the current tree.


## Donor-olean await result (2026-11-14, read-only)

Checked watchdog status for the candidate route file
`LeanFormal/IUT/Foundations/AlgebraicGeometry/GeneralNormalizedNormBySpectralUniqueness.lean`
(the file containing `generalNormalizedNormFormula` and
`normalizedCanonicalPowerComparison`).

Result: **no olean; donor build fails, and it cannot build as currently written.**

- First failure: missing dependency olean
  `LeanFormal/IUT/Foundations/AlgebraicGeometry/BaseScalarValuationRelation.olean`
  (that module is in `extra-targets.txt` but has no olean yet).
- A second, structural blocker remains even after that dependency exists:
  `GeneralNormalizedNormBySpectralUniqueness.lean:94` uses
  `canonicalAbsValue_add_le`, but that theorem is defined in
  `CanonicalAbsValueAddLeProof.lean:64`, and
  `CanonicalAbsValueAddLeProof.lean` itself starts with
  `import ...GeneralNormalizedNormBySpectralUniqueness`.  This is a circular
  dependency: General does not import AddLeProof, so `canonicalAbsValue_add_le`
  is an unknown identifier in General; AddLeProof imports General, so the two
  files cannot be ordered from their current content.

**Formula match check (source-level, pending build).**  If the donor were built,
its statements do match the expected relation:

- `GeneralNormalizedNormBySpectralUniqueness.generalNormalizedNormFormula`:
  `||x||_normalized = absNorm ^ (-(nu x) / d)`, with
  `nu x = -log (Valued.v x)` and `d = relativeCompletionDegree (k := Q) place`.
- `FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow` (green):
  `||x||_default = absNorm ^ m`, where `m = log (Valued.v x) = -nu x`.
- Therefore the donor formula is exactly
  `||x||_normalized = ||x||_default ^ (1/d)`, matching the expected relation in
  the main note.  `normalizedCanonicalPowerComparison` is the equivalent
  `||x||_normalized ^ d = ||x||_default` spelling.

**Route to make the donor buildable:** move `canonicalAbsValue`, `nu`,
`absNorm_gt_one`, `d_eq_e_mul_f` and the `canonicalAbsValue_add_le` proof into a
lower shared module (or inline the add_le proof into
`GeneralNormalizedNormBySpectralUniqueness`), then let
`CanonicalAbsValueAddLeProof` import the built donor; also build
`BaseScalarValuationRelation` first.  Until then, `NormValuationCompatible` stays
unproved and the qVFamily norm-instance gap remains conditional/ratio-explicit.


## BaseScalar deps check (2026-11-14, read-only)

Donor `GeneralNormalizedNormBySpectralUniqueness` still has no olean.  Its blocked
dependency `BaseScalarValuationRelation.lean` also has no olean, and this is **not**
a missing-import situation:

- All five imports of `BaseScalarValuationRelation.lean` already have oleans:
  `FinitePlaceExtension`, `FinitePlacePadicScalarStructure`,
  `Example36CompletionNormFormulaActual`, `Mathlib.NumberTheory.Padics.PadicIntegers`,
  `PadicScalarValuationConstruction`.
- The file itself fails at proof/instance level.  First error:
  `BaseScalarValuationRelation.lean:125:6: rewrite failed`, pattern
  `↑↑(PadicInt.mkUnits hunorm)` not found in target
  `q = ↑↑(pNat place)^m * (algebraMap ℤ_[pNat place] (scalarField place)) ↑(PadicInt.mkUnits hunorm)`;
  Lean notes the target is not type-correct under the `instances` transparency level,
  i.e. an instance-unfolding/defeq issue.
- Additional errors at lines 140 (`unsolved goals`), 146/151
  (`synthesized type class instance is not definitionally equal ...`), and 167
  (`Application type mismatch`).

So the donor chain is blocked by an upstream proof/instance issue, not by a missing
olean.  The formula comparison remains source-level: if the donor were built,
`generalNormalizedNormFormula` (`||x||_normalized = absNorm^(-nu/d)`) plus the green
default formula `norm_eq_absNorm_zpow` (`||x||_default = absNorm^m`, `m = -nu`) gives
`||x||_normalized = ||x||_default^(1/d)`, matching the expected relation.
Next route: fix the BaseScalar instance/rewrite errors first, then the donor circular
dependency described above.
