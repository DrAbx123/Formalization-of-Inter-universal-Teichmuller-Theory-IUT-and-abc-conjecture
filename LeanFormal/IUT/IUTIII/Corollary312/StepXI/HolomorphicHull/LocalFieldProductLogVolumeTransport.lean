import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHullTransport
import LeanFormal.IUT.Foundations.LocalFields.NormalizedHaarTransport

/-!
# Numerical log-volume compatibility for topological field-product equivalences

The source and target may carry different Haar measures. A topological ring
equivalence preserves the actual unit regions. Haar uniqueness then cancels
the measure-scaling factor in the signed, unit-relative log-volume. The hull
specialization supplies its own positive finite mass from compactness and
coordinate nondegeneracy.
-/

namespace LeanFormal.IUT.LocalFieldProductHull

open MeasureTheory

noncomputable section

variable {J L : Type*} {E : J → Type*} {F : L → Type*}
variable [∀ j, NormedField (E j)] [∀ l, NormedField (F l)]

def productFieldContinuousAddEquiv
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm) :
    ((j : J) → E j) ≃ₜ+ ((l : L) → F l) where
  toAddEquiv := e.toAddEquiv
  continuous_toFun := he
  continuous_invFun := hinverse

variable [Finite J] [Finite L] [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]
variable [MeasurableSpace ((j : J) → E j)] [BorelSpace ((j : J) → E j)]
variable [MeasurableSpace ((l : L) → F l)] [BorelSpace ((l : L) → F l)]

omit [Finite L] [∀ l, ProperSpace (F l)]
  [BorelSpace ((j : J) → E j)]
  [MeasurableSpace ((l : L) → F l)] [BorelSpace ((l : L) → F l)] in
theorem measure_unitRegion_pos_lt_top
    (μ : Measure ((j : J) → E j)) [Measure.IsAddHaarMeasure μ] :
    0 < μ (unitRegion (K := E)) ∧ μ (unitRegion (K := E)) < ⊤ := by
  have heq : unitRegion (K := E) = region (1 : (j : J) → E j) := by
    ext x
    simp only [unitRegion, region, Pi.one_apply, norm_one]
  rw [heq]
  exact ⟨measure_region_pos μ 1 (fun _ => one_ne_zero), measure_region_lt_top μ 1⟩

theorem normalizedLogVolume_continuous_ringEquiv
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm)
    (μ : Measure ((j : J) → E j)) (ν : Measure ((l : L) → F l))
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S : Set ((j : J) → E j)} (hS : IsCompact (closure S)) (hpos : 0 < μ S) :
    normalizedLogVolume ν (e '' S) = normalizedLogVolume μ S := by
  have hlog := NormalizedHaarTransport.relative_log_mass_image_eq
    (productFieldContinuousAddEquiv e he hinverse) μ ν hS
    (isCompact_unitRegion (K := E)).closure hpos (measure_unitRegion_pos_lt_top μ).1
  change Real.log (ν (e '' S)).toReal - Real.log (ν (e '' unitRegion (K := E))).toReal =
    Real.log (μ S).toReal - Real.log (μ (unitRegion (K := E))).toReal at hlog
  rw [continuous_ringEquiv_image_unitRegion e he hinverse] at hlog
  exact hlog

theorem normalizedLogVolume_hull_continuous_ringEquiv
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm)
    (μ : Measure ((j : J) → E j)) (ν : Measure ((l : L) → F l))
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν]
    {S : Set ((j : J) → E j)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ j, ∃ x ∈ S, x j ≠ 0) :
    normalizedLogVolume ν (hull (e '' S)) = normalizedLogVolume μ (hull S) := by
  obtain ⟨lam, _, heq⟩ := exists_hull_eq_region_of_isCompact_closure hS hne hcoord
  have hcompact : IsCompact (hull S) := by rw [heq]; exact isCompact_region lam
  rw [← continuous_ringEquiv_image_hull e he hinverse S]
  exact normalizedLogVolume_continuous_ringEquiv e he hinverse μ ν hcompact.closure
    (measure_hull_pos_lt_top μ hS hne hcoord).1

theorem addHaar_normalizedLogVolume_hull_continuous_ringEquiv
    (e : ((j : J) → E j) ≃+* ((l : L) → F l))
    (he : Continuous e) (hinverse : Continuous e.symm)
    {S : Set ((j : J) → E j)} (hS : IsCompact (closure S)) (hne : S.Nonempty)
    (hcoord : ∀ j, ∃ x ∈ S, x j ≠ 0) :
    normalizedLogVolume (Measure.addHaar : Measure ((l : L) → F l)) (hull (e '' S)) =
      normalizedLogVolume (Measure.addHaar : Measure ((j : J) → E j)) (hull S) :=
  normalizedLogVolume_hull_continuous_ringEquiv e he hinverse Measure.addHaar Measure.addHaar
    hS hne hcoord

end

end LeanFormal.IUT.LocalFieldProductHull
