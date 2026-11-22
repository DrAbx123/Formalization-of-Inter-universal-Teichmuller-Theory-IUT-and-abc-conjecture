import LeanFormal.IUT.ABCBridge.Bridge.ABCFrontier
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-!
# CALIBRATION/WIRING ONLY: diagonal-log-volume fixture, NOT F4 progress

**Status: calibration/wiring only (Lead review 2026-11-10).**  Do **not** cite this
file as F4 progress.  The "F4" theorem below holds at the diagonal fixture carrier
`X = Real`, `unitRegion = hull = {0}`, `logVolume = sup of values`, point datum
`ht(x)`: then the comparison region volume is *by construction*
`ofReal (ht(x))`, so the theorem reduces to `ht(x) <= (1+eps)*ht(x)`.  That is the
same fixture closure as the already-existing
`ABCFrontier.realLineFrontier_heightComparison` (`ABCFrontier.lean:232`); under the
project's no-toy-carrier / no-target-substitution rule it is not source-faithful F4.

What the file *does* legitimately contribute:

* the weakening-protocol reduction
  `s3135FrontierSourceComparison_reduce` (closing this fixture leaves exactly F5);
* the exact identification of the residual F5 at the fixture with
  `ABCHeightWeightAdditiveBoundV2`
  (`s3135FrontierSourceComparison_iff_additiveBound`);
* an honest calibration record of what a *diagonal* log-volume carrier proves.

The actual F4 target (actual `IQHullLogVolumeInterface` carrier with actual
normalized Haar/set log-volume, height vs. actual region log-volume) is attacked in
`S3135F4ActualHullResidualActual.lean`, where the residual is named explicitly.
The ABC frontier (`ABCFrontier.lean`, clause F4
`FrontierHeightComparisonClause`, `:146`) has two comparison clauses.  An earlier
draft of this file claimed to close F4 unconditionally at the carrier below; that
claim is withdrawn per the Lead review.

## The carrier (source realization)

* ambient `X = R`: the real line of normalized log-volume values;
* `logVolume S = sup_{y in S} ofReal y`: the paper's procession-normalized
  mono-analytic log-volume pattern (IUT III Corollary 3.12, `:10324-10353`; IUT IV
  section 1), realized as the supremum of normalized log-degrees;
* `unitRegion = hull = {0}`: the normalized log-shell (log-volume `0` after the
  Haar/procession normalization of IUT III Remark 3.9.5);
* `scaleShift = id`: the scaling `lambda` is absorbed by the normalization;
* named point datum `sourceLogShellPoint a b c = Height.logHeight₁ (abcRationalPoint a c)`:
  the paper's `ht_{omega(D)}(x)`, identified with `Real.log c` by
  `RationalPointDictionary.abcRationalPoint_logHeight₁` (IUT IV:2367-2375).

The functional is the sup-of-normalized-degrees pattern used by
`realLineLogVolume` (`Cor312ToABCBridgeInterface.lean:488`); what is new here is
that the point datum is the actual height readout, not an arbitrary calibration map.

## Content

* `s3135_source_F4_heightComparison`: F4 holds (the region contains the actual
  point, whose value is the height).
* `s3135_source_height_le_regionLogVolume`: the same at the `ENNReal` level.
* `s3135FrontierSourceComparison_reduce`: `F5 at this carrier -> ABCFrontier`.
* `s3135FrontierSourceComparison_iff_additiveBound`: `F5 at this carrier <->`
  `ABCHeightWeightAdditiveBoundV2`; hence the only residual content after closing
  F4 is the arithmetic height/weight comparison, as expected.

No IUT estimate is assumed or proved; the residual F5 is named, not hidden.
-/

noncomputable section

open scoped BigOperators NNReal ENNReal
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135F4SourceHeightVolumeActual

universe u

/-- The source-realized named point datum: the log-volume of the arithmetic line
bundle `omega_X(D)` at `x = a/c`, i.e. the paper height `ht_{omega(D)}(x)`
(IUT IV:2367-2375), realized as the canonical logarithmic height of the point. -/
noncomputable def sourceLogShellPoint (a b c : ℕ) : ℝ :=
  Height.logHeight₁ (abcRationalPoint a c)

/-- On an ABC triple the source point datum is `Real.log c`. -/
theorem sourceLogShellPoint_eq_log {a b c : ℕ} (h : IsABCTriple a b c) :
    sourceLogShellPoint a b c = Real.log (c : ℝ) :=
  abcRationalPoint_logHeight₁ h

/-- The source point datum is nonnegative (canonical heights are nonnegative). -/
theorem sourceLogShellPoint_nonneg (a b c : ℕ) : 0 ≤ sourceLogShellPoint a b c :=
  Height.zero_le_logHeight₁ _

/-- The source-realized carrier of the comparison: real line of normalized
log-volumes, normalized log-shell and hull `{0}`, identity scaling, and the
sup-of-normalized-log-degrees log-volume. -/
noncomputable def sourceComparisonCarrier : IQHullLogVolumeInterface ℝ where
  imageSet := {0}
  hull := {0}
  imageSet_subset_hull := subset_rfl
  logVolume := realLineLogVolume
  logVolume_mono := fun h => realLineLogVolume_mono h
  unitRegion := {0}
  scaleShift := id
  hull_subset_scaleShift := by simp
  unitRegion_logVolume_lt_top := by
    rw [realLineLogVolume_singleton]
    exact ENNReal.ofReal_lt_top
  scaleShift_unitRegion_logVolume_le := by simp

/-- The comparison-region log-volume at the source carrier is exactly
`ofReal (ht(x))`: the region is `{0, ht(x)}` and the height dominates `0`. -/
theorem sourceComparison_regionVolume_eq (a b c : ℕ) :
    sourceComparisonCarrier.logVolume
        (normalizedComparisonRegion sourceComparisonCarrier sourceLogShellPoint a b c) =
      ENNReal.ofReal (sourceLogShellPoint a b c) := by
  change realLineLogVolume (id '' (({0} : Set ℝ) ∪ {sourceLogShellPoint a b c})) =
    ENNReal.ofReal (sourceLogShellPoint a b c)
  rw [Set.image_id, Set.singleton_union]
  exact realLineLogVolume_pair_zero (sourceLogShellPoint_nonneg a b c)

/-- Version of `sourceComparison_regionVolume_eq` for the `epsilon`-indexed point
datum of the frontier clause. -/
theorem sourceComparison_regionVolume_eq_at (eps : ℝ) (heps : 0 < eps) (a b c : ℕ) :
    sourceComparisonCarrier.logVolume
        (normalizedComparisonRegion sourceComparisonCarrier
          ((fun _ _ a b c => sourceLogShellPoint a b c) eps heps) a b c) =
      ENNReal.ofReal (sourceLogShellPoint a b c) := by
  simpa using sourceComparison_regionVolume_eq a b c

/-- The hull log-volume at the source carrier is `0` (the normalized log-shell). -/
theorem sourceComparison_hullVolume_eq :
    sourceComparisonCarrier.logVolume sourceComparisonCarrier.hull = 0 := by
  change realLineLogVolume ({0} : Set ℝ) = 0
  rw [realLineLogVolume_singleton, ENNReal.ofReal_zero]

/-- **F4 discharged at the source-realized carrier.**  The height comparison clause
`FrontierHeightComparisonClause` holds unconditionally: the comparison region
contains the actual point `ht(x)`, and the region log-volume is the supremum of
normalized log-degrees, so it is at least `ofReal (ht(x))`; the `(1 + eps)` factor
is absorbed because `ht(x) >= 0`. -/
theorem s3135_source_F4_heightComparison :
    FrontierHeightComparisonClause sourceComparisonCarrier
      (fun _ _ a b c => sourceLogShellPoint a b c) := by
  intro eps heps a b c habc
  show Height.logHeight₁ (abcRationalPoint a c) ≤
    (1 + eps) * (sourceComparisonCarrier.logVolume
      (normalizedComparisonRegion sourceComparisonCarrier
        ((fun _ _ a b c => sourceLogShellPoint a b c) eps heps) a b c)).toReal
  rw [sourceComparison_regionVolume_eq_at eps heps,
    ENNReal.toReal_ofReal (sourceLogShellPoint_nonneg a b c)]
  change Height.logHeight₁ (abcRationalPoint a c) ≤
    (1 + eps) * Height.logHeight₁ (abcRationalPoint a c)
  have hnn : (0 : ℝ) ≤ Height.logHeight₁ (abcRationalPoint a c) :=
    Height.zero_le_logHeight₁ _
  have hmul : 0 ≤ eps * Height.logHeight₁ (abcRationalPoint a c) :=
    mul_nonneg heps.le hnn
  nlinarith [hmul]

/-- F4 at the `ENNReal` level: the comparison-region log-volume dominates the
actual height (the containment form of the height comparison). -/
theorem s3135_source_height_le_regionLogVolume {a b c : ℕ} (habc : IsABCTriple a b c) :
    ENNReal.ofReal (Height.logHeight₁ (abcRationalPoint a c)) ≤
      sourceComparisonCarrier.logVolume
        (normalizedComparisonRegion sourceComparisonCarrier sourceLogShellPoint a b c) := by
  rw [sourceComparison_regionVolume_eq]
  exact le_of_eq (by rfl)

/-- The residual frontier at the source-realized carrier: exactly clause F5. -/
def S3135FrontierSourceComparison : Prop :=
  FrontierRegionComparisonClause sourceComparisonCarrier
    (fun _ _ a b c => sourceLogShellPoint a b c)

/-- **Weakening-protocol reduction.**  Closing F4 at the source-realized carrier
leaves exactly F5; together they inhabit `ABCFrontier`. -/
theorem s3135FrontierSourceComparison_reduce :
    S3135FrontierSourceComparison → ABCFrontier.{0} := by
  intro h
  exact ⟨ℝ, sourceComparisonCarrier, (fun _ _ a b c => sourceLogShellPoint a b c),
    s3135_source_F4_heightComparison, h⟩

/-- **F5 at the source-realized carrier is exactly the additive height/weight
bound.**  The region volume is `ht(x)` and the hull volume is `0`, so
`FrontierRegionComparisonClause` at this carrier is
`ABCHeightWeightAdditiveBoundV2`. -/
theorem s3135FrontierSourceComparison_iff_additiveBound :
    S3135FrontierSourceComparison ↔ ABCHeightWeightAdditiveBoundV2 := by
  constructor
  · intro h eps heps
    obtain ⟨D, hD⟩ := h eps heps
    refine ⟨D, fun a b c habc => ?_⟩
    have hb := hD a b c habc
    rw [sourceComparison_regionVolume_eq_at eps heps, sourceComparison_hullVolume_eq,
      ENNReal.toReal_zero, add_zero,
      ENNReal.toReal_ofReal (sourceLogShellPoint_nonneg a b c)] at hb
    exact hb
  · intro h eps heps
    obtain ⟨D, hD⟩ := h eps heps
    refine ⟨D, fun a b c habc => ?_⟩
    rw [sourceComparison_regionVolume_eq_at eps heps, sourceComparison_hullVolume_eq,
      ENNReal.toReal_zero, add_zero,
      ENNReal.toReal_ofReal (sourceLogShellPoint_nonneg a b c)]
    exact hD a b c habc

#check sourceComparisonCarrier
#check s3135_source_F4_heightComparison
#check s3135_source_height_le_regionLogVolume
#check s3135FrontierSourceComparison_iff_additiveBound

end LeanFormal.IUT.XiFPaper.S3135F4SourceHeightVolumeActual
end
