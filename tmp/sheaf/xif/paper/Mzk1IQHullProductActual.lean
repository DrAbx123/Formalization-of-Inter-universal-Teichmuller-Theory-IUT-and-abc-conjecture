import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option maxHeartbeats 2000000

/-!
# Mzk1IQHullProductActual — an IQHullLogVolumeInterface realized from product local fields

DAG node: iutiv-abc:IQHull (interface, CONDITIONAL, 1 unproved dep).  This file advances
the node by *realizing* the interface from the existing REAL product-local-field hull layer
(LocalFieldProductHull):

* imageSet : S (relatively compact);
* hull : LocalFieldProductHull.hull S (paper intersection of lambda*O regions);
* logVolume : clamped normalized Haar log-volume (clamped so the total functional stays
  monotone without positivity hypotheses on every set);
* unitRegion / scaleShift : product unit balls and multiplicative dilation by lambda, using
  hull = region lambda;
* scaling inequality proved under the explicit paper-faithful hypothesis that the
  distributive Haar character of lambda has nonpositive logarithm.

The literal paper carrier IQ(...) remains named.  No closure claim; gate NOT PASSED.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IQHullProductActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldProductHull
open MeasureTheory

universe u

variable {ι : Type*} [Fintype ι] {K : ι → Type*} [∀ i, NormedField (K i)]
  [∀ i, ProperSpace (K i)]
  [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
  (μ : Measure ((i : ι) → K i)) [Measure.IsAddHaarMeasure μ]

/-- Clamped normalized Haar log-volume: zero-mass sets get 0, infinite-mass sets get top,
finite positive-mass sets get ENNReal.ofReal of the normalized log-volume. -/
noncomputable def productLogVolume (S : Set ((i : ι) → K i)) : ENNReal :=
  if _h0 : μ S = 0 then 0
  else if _htop : μ S = ⊤ then ⊤
  else ENNReal.ofReal (LocalFieldProductHull.normalizedLogVolume μ S)

/-- The clamped log-volume is monotone under inclusion. -/
theorem productLogVolume_mono [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] {S T : Set ((i : ι) → K i)} (hST : S ⊆ T) :
    productLogVolume (K := K) μ S ≤ productLogVolume (K := K) μ T := by
  unfold productLogVolume
  by_cases hS0 : μ S = 0
  · rw [dif_pos hS0]
    exact bot_le
  · have hSpos : 0 < μ S := lt_of_le_of_ne bot_le (Ne.symm hS0)
    by_cases hStop : μ S = ⊤
    · rw [dif_neg hS0, dif_pos hStop]
      exact le_top
    · rw [dif_neg hS0, dif_neg hStop]
      have hTne0 : μ T ≠ 0 := by
        intro hT0
        apply hS0
        exact le_antisymm (hT0 ▸ measure_mono hST) bot_le
      by_cases hTtop : μ T = ⊤
      · rw [dif_pos hTtop]
        exact le_top
      · rw [dif_neg hTne0, dif_neg hTtop]
        exact ENNReal.ofReal_le_ofReal
          (LocalFieldProductHull.normalizedLogVolume_mono μ hST hSpos
            (lt_top_iff_ne_top.mpr hTtop))

/-- The product unit region is the region of the all-ones scaling. -/
theorem unitRegion_eq_region_one :
    LocalFieldProductHull.unitRegion (K := K) =
      LocalFieldProductHull.region (fun _ : ι => (1 : K _)) := by
  ext x
  simp [LocalFieldProductHull.unitRegion, LocalFieldProductHull.region]

/-- The unit region has normalized log-volume zero. -/
theorem productLogVolume_unitRegion_eq_zero [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] :
    productLogVolume (K := K) μ (LocalFieldProductHull.unitRegion (K := K)) = 0 := by
  rw [unitRegion_eq_region_one]
  have hpos : 0 < μ (LocalFieldProductHull.region (fun _ : ι => (1 : K _))) :=
    LocalFieldProductHull.measure_region_pos μ (fun _ => (1 : K _)) (fun _ => one_ne_zero)
  have hfin : μ (LocalFieldProductHull.region (fun _ : ι => (1 : K _))) < ⊤ :=
    LocalFieldProductHull.measure_region_lt_top μ (fun _ => (1 : K _))
  unfold productLogVolume
  rw [dif_neg (ne_of_gt hpos), dif_neg (ne_of_lt hfin)]
  rw [unitRegion_eq_region_one]
  rw [LocalFieldProductHull.normalizedLogVolume_unitRegion]
  simp

/-- The unit region has finite log-volume. -/
theorem productLogVolume_unitRegion_lt_top [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] :
    productLogVolume (K := K) μ (LocalFieldProductHull.unitRegion (K := K)) < ⊤ := by
  rw [productLogVolume_unitRegion_eq_zero μ]
  exact ENNReal.zero_lt_top

/-- A lambda*O region has log-volume zero under the nonpositive Haar-character hypothesis. -/
theorem productLogVolume_region_eq_zero [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] (lam : (i : ι) → K i)
    (hlam : ∀ i, lam i ≠ 0)
    (hchar : Real.log (distribHaarChar ((i : ι) → K i)
      (LocalFieldProductHull.scalingUnits lam hlam) : ℝ) ≤ 0) :
    productLogVolume (K := K) μ (LocalFieldProductHull.region lam) = 0 := by
  have hpos : 0 < μ (LocalFieldProductHull.region lam) :=
    LocalFieldProductHull.measure_region_pos μ lam hlam
  have hfin : μ (LocalFieldProductHull.region lam) < ⊤ :=
    LocalFieldProductHull.measure_region_lt_top μ lam
  unfold productLogVolume
  rw [dif_neg (ne_of_gt hpos), dif_neg (ne_of_lt hfin)]
  rw [LocalFieldProductHull.normalizedLogVolume_region μ lam hlam]
  exact ENNReal.ofReal_of_nonpos hchar

/-- **Realization of IQHullLogVolumeInterface from product local fields.** -/
theorem exists_iqHullLogVolumeInterface_of_product [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ]
    {S : Set ((i : ι) → K i)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ i, ∃ x ∈ S, x i ≠ 0)
    (lam : (i : ι) → K i) (hlam : ∀ i, lam i ≠ 0)
    (hull_eq : LocalFieldProductHull.hull S = LocalFieldProductHull.region lam)
    (hchar : Real.log (distribHaarChar ((i : ι) → K i)
      (LocalFieldProductHull.scalingUnits lam hlam) : ℝ) ≤ 0) :
    Nonempty (IQHullLogVolumeInterface ((i : ι) → K i)) := by
  have hunit : productLogVolume (K := K) μ
      (LocalFieldProductHull.unitRegion (K := K)) = 0 :=
    productLogVolume_unitRegion_eq_zero μ
  refine ⟨⟨S, LocalFieldProductHull.hull S, LocalFieldProductHull.subset_hull S,
    productLogVolume (K := K) μ, ?_, LocalFieldProductHull.unitRegion (K := K),
    (fun x => lam * x), ?_, productLogVolume_unitRegion_lt_top μ, ?_⟩⟩
  · intro S' T' hST
    exact productLogVolume_mono μ hST
  · rw [hull_eq, ← LocalFieldProductHull.region_eq_mul_unitRegion lam hlam]
    exact subset_rfl
  · rw [← LocalFieldProductHull.region_eq_mul_unitRegion lam hlam]
    rw [productLogVolume_region_eq_zero μ lam hlam hchar, hunit]
    exact le_rfl

end LeanFormal.IUT.XiFPaper.Mzk1IQHullProductActual

end
