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


## BaseScalar errors route (2026-11-14, read-only)

The latest watchdog run of `BaseScalarValuationRelation.lean` still fails; its imports are all built.  Error map and suggested fixes (no edits made):

| Location | Error | Cause / route |
|---|---|---|
| `:46:2` | `isDefEq` timeout (2.4M heartbeats) | local instance `padicScalarValuedInstance` unfolds `padicScalarValued`; try defining it via `inferInstanceAs`/explicit structure or raising local heartbeats only for this instance. |
| `:49:2` | expected `Fact (Nat.Prime (pNat place))`, got `Nat.Prime ↑(completionRationalPrime place)` | `pNat` is the `Nat.Primes.val`; wrap the proof: `⟨(completionRationalPrime place).property⟩`, not `.2`. |
| `:59:2` | `simpa` gives `True`, expected `Valued.v ↑(pNat place) = (WithZero.exp 1)⁻¹` | `Rat.padicValuation_self` simplification is under a different `Valued` instance/coercion; use an explicit `have`/`change` in the `Valued.v` spelling of `Completion (comap place)`, or route through `Padic.norm_eq_zpow_neg_valuation`. |
| `:113:24` | unsolved `¬ pNat place = 0` | `simp [p]` stopped at Nat level; close with `(Fact.out : Nat.Prime (pNat place)).ne_zero` or `Nat.cast_ne_zero.mpr`. |
| `:118:4` | `No goals to be solved` | `rw [Padic.norm_eq_zpow_neg_valuation hq]` already closes; remove the following `rfl`. |
| `:121:8` | invalid rewrite argument `uq` is a value | `uq` is a local `let`; use `dsimp only [uq]`/`change` instead of `rw [uq, ...]`; also the same run reports instance transparency (Nat.Primes vs subtype) in the `scalarPrime_norm` rewrite. |
| `:125:6` | rewrite pattern `↑↑(PadicInt.mkUnits hunorm)` not found; target is `(algebraMap ℤ_[pNat] (scalarField)) ↑(mkUnits hunorm)` | `PadicInt.mkUnits_eq` is in coercion spelling; `change` the goal to `q = p^m * ((mkUnits hunorm : ℤ_[pNat]) : scalarField)` first, then rewrite, or prove a helper equality in `algebraMap` spelling. |
| `:146:5`, `:151:9` | synthesized instance not defeq: `DivisionRing.toRatAlgebra` vs `IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion` | The `rationalCompletionPadicEquiv`/`completionMap` path uses a different `Algebra ℚ completionField` instance than the `algebraMap` in the goal.  Do not rewrite across them directly; introduce the explicit `letI : Algebra ℚ completionField := ...` used by `completionMap`, then `change` both sides to the `completionMap` spelling. |
| `:140:0` | unsolved goals in `unitUpperValuation` | After `rw [← h]`, the lower-unit valuation/`one_pow` rewrite order leaves the goal; split into the two factors (prime and unit) explicitly with `map_mul`/`map_zpow₀` and close the lower unit valuation by `padicUnit_valuation_zero`. |
| `:167:27` | `Classical.choose (scalarDVRDecomposition place q hq)` has type `∃ u, ...`, expected `∃ x : ℤ_[pNat], ...` | The theorem result is nested `∃ m, ∃ u, ...`; `Classical.choose` returns `m`.  Restate the target as `∃ m u, ... ∧ ...`, or choose the inner witness via `Classical.choose (Classical.choose_spec (scalarDVRDecomposition place q hq))`. |

Route order: fix `pNat`/`Fact` (`:49`) and the local `Valued` instance (`:46`) first, then the `let`/rewrite/coercion block `:113–:125`, then the completion-map instance defeq block `:140–:151`, then the nested-exists statement `:167`.  Only after `BaseScalarValuationRelation` is green can the donor `GeneralNormalizedNormBySpectralUniqueness` be built; its circular dependency (`canonicalAbsValue_add_le`) must then also be fixed.  Until then, `NormValuationCompatible` remains unproved and the norm-instance gap stays conditional/ratio-explicit.

## BSR route — latest read-only update (2026-11-14 12:50)

`BaseScalarValuationRelation.lean` is being edited concurrently (source mtime 12:48,
latest compile log 12:46), so the error list is a moving target.  The latest compiled
run still had no olean; current-first errors and routes:

- `:101:34`: `zpow_eq_one_iff_right₀` needs **two** arguments in this Mathlib pin:
  `(ha₀ : 0 ≤ a) (ha₁ : a ≠ 1)`.  Current code passes only `hpgt`; use
  `zpow_eq_one_iff_right₀ (show (0:ℝ) ≤ (pNat place:ℝ) by positivity)`
  `(by exact_mod_cast ...one_lt.ne')` (or `.ne'` of `hpgt`).
- `:113:24`: still `simp [p]` leaves `¬pNat place = 0`; close with
  `(Fact.out : Nat.Prime (pNat place)).ne_zero` or `Nat.cast_ne_zero.mpr`.
- `:120:8`: `rw [uq, ...]` on a local `let`; use `dsimp only [uq]`/`change`, not `rw`.
- `:125:4`: current edit uses `PadicInt.mkUnits_coe hunorm`, which is **unknown**;
  the green Mathlib lemma is `PadicInt.mkUnits_eq`
  (`((mkUnits h : ℤ_[p]) : ℚ_[p]) = u`).  Since the goal has the `algebraMap` spelling,
  `change` the goal to the coercion spelling first, then use `PadicInt.mkUnits_eq`.
- `:143:46`: bare `instAlgebraAdicCompletion` is a function of place/prime, not an
  `Algebra ℚ (completionField place)` term; do not bind it as `letI`.  Use the
  already-inferred completion algebra instance, or avoid the `letI` and rewrite via
  `completionMap` directly.
- `:146:5`, `:151:9`: unchanged instance defeq mismatch
  (`DivisionRing.toRatAlgebra` vs `instAlgebraAdicCompletion`); rewrite the goal to the
  literal `completionMap` spelling with `change`/`show` under the same instance, instead
  of rewriting an `algebraMap` equality across instances.
- `:139:0` / `:174:8`: `unitUpperValuation` and `baseScalarValuationRelation` still have
  unsolved goals/motive errors.  For `:174`, the current source statement uses explicit
  `∃ m, ∃ u`, so after `obtain ⟨m,u,hdec⟩` use `refine ⟨m,u,?_,?_⟩` (not an inner
  `refine ⟨hdec,_⟩` if the goal already carries a dependent/choose expression); for
  `:139`, split `map_mul`/`map_zpow₀` and close the lower unit valuation via
  `padicUnit_valuation_zero` before `one_pow`.

No edits made; this is a route record for the owner of the file.  Once BSR is green, the
donor still needs the circular-dependency fix; formula comparison remains source-level
matching `normalized = default^(1/d)`.

## BSR route — 13:00 read-only update

Latest compiled run of `BaseScalarValuationRelation.lean` still fails (no olean).
The file has been edited again (new sections around lines 281-349); latest errors:

- `:290:4` `No goals to be solved`: the preceding `congr 1` already closed the goal;
  remove the following `exact ...coe_padicIntEquiv_symm_apply...` (or move it before the
  `congr` if it is the intended closing term).
- `:329:14` rewrite failed for the `completionMap_coe` pattern: the goal is in a
  `show`-normalized `completionMap (padicEquiv.symm ...)` form.  Use `change` to the
  literal `completionMap` argument spelling, or `simp only [completionMap_coe]` once
  the argument is a definitional `completionMap` application.
- `:343:6` unknown `Algebra.algebraMap.coe_zpow`: this lemma does not exist in the pin.
  The zpow transport is already covered by `map_zpow₀` on the next line; drop
  `:343` (or replace by `map_zpow₀` with the appropriate ring hom).
- `:307:60` unsolved goals at the theorem statement is a downstream symptom: the proof
  body does not close after the above rewrites; fix `:290/`:329/`:343` first, then
  re-check the final `WithZero.exp`/ring step.

The route order is unchanged: make BSR green first (these are proof-level edits, not
missing imports), then fix the donor's circular dependency.  Formula comparison remains
source-level matching `normalized = default^(1/d)`.

## BSR route — 13:20 read-only update

No olean yet; latest compiled run failed 13:17.  The source has been edited further
(now using `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` and
`algebraMap_ratCast_eq'`); current errors:

- `:161:8` rewrite failed for `algebraMap_ratCast_eq'`: the target prints
  `algebraMap ℚ (adicCompletion ...) ↑(pNat place)` (Nat cast path), while the lemma
  pattern has `↑↑(pNat place)` (Nat→Rat→field).  Use `map_natCast`/`algebraMap_natCast`
  or normalize the cast path with `push_cast`/`norm_num` before rewriting.
- `:335:69` unsolved goals in the first `calc` step of `hcomp`:
  after `rw [scalarAlgebra_algebraMap]` the goal is not closed by `rfl`.
  Unfold `padicCompletionHom` explicitly (`change`/`dsimp only [padicCompletionHom]`)
  so both sides are the same `completionMap (padicEquiv.symm ...)` term.
- `:306:60`, `:311:60`, `:317:60` unsolved goals at the theorem statements are
  downstream symptoms of the same unfinished `hcomp`/final valuation proof; they should
  disappear once the calc and the Nat-vs-Rat cast rewrite are fixed.
- The earlier `:290`, `:329`, `:343` errors are no longer present in the latest run
  (the concurrent edits addressed them).

Route order unchanged: finish the `hcomp` calc (cast path + `padicCompletionHom`
unfolding), then the final `WithZero.exp`/ring step; only then can BSR produce an olean
and unblock the donor.  Formula comparison remains source-level
`normalized = default^(1/d)`.

## BSR status and donor restructure route (2026-11-14 13:40, read-only)

**BSR is now green:** `BaseScalarValuationRelation.olean` exists
(watchdog DONE 13:22:40).  So the upstream blocker reported earlier is cleared.

**Donor still has no olean**; latest donor failure 13:32 is now a restructure/type
issue, not the old BSR blocker:

1. `:61:2` unknown `relativeCompletionDegree_eq_ramificationIdx_mul_inertiaDeg`:
   the theorem lives in `FinitePlaceCompletionDegreeGlobal.lean`, which the donor
   does not import.  Add
   `import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionDegreeGlobal`.
2. `:64:52`, `:98:49`, `:100:20`, `:123:47`, `:130:42`, `:139:10`, `:142:8`:
   the aliases
   `abbrev K : Type u := PadicScalarField place` and
   `abbrev L : Type u := place.maximalIdeal.adicCompletion F`
   are now **functions of `place`** (Lean auto-binds the free `place`), but the file
   uses `K` and `L` as bare types:
   `AbsoluteValue L`, `(q : K)`, `spectralNorm K L`, `∀ x : L`.
   Fix by applying the parameter consistently — `AbsoluteValue (L place)`,
   `(q : K place)`, `spectralNorm (K place) (L place)`, `∀ x : L place` — or make the
   aliases take explicit arguments and update all uses.
3. The earlier circular dependency is still present: `:94` calls
   `canonicalAbsValue_add_le`, defined in `CanonicalAbsValueAddLeProof.lean`, which
   imports the donor.  After the type/import fixes, the cycle must be removed by
   moving `canonicalAbsValue`/`nu`/`absNorm_gt_one`/`d_eq_e_mul_f` (and the
   `add_le` proof) into a shared lower module, or by inlining the `add_le` proof in the
   donor and making AddLeProof import the donor.

After BSR green + these two restructure fixes + the cycle fix, the donor can build and
the formula comparison can be verified at olean level.  Source-level formula remains
`||x||_normalized = absNorm^(-nu/d)`, and with the green default formula this gives
`normalized = default^(1/d)`.
