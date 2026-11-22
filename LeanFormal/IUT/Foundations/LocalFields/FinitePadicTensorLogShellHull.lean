import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHullSpan

/-!
# The actual finite logarithmic tensor image has a genuine integral hull

Map the compact pure log-shell region through a finite field-product
decomposition. Its identity makes every coordinate nondegenerate. The
existing smallest lambda*O construction then gives a compact integral
module hull with positive finite Haar mass and signed log-volume.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Finite ι]
variable (A : ι → Type) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]
variable {J : Type} [Finite J] {E : J → Type}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]

def tensorLogShellProductImage
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Set ((j : J) → E j) := e '' tensorLogShellRegion (p := p) A

omit [Finite J] in
theorem isCompact_tensorLogShellProductImage
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (tensorLogShellProductImage A e) := by
  letI := Fintype.ofFinite ι
  exact (isCompact_tensorLogShellRegion A).image e.toLinearMap.continuous_of_finiteDimensional

omit [Finite ι] [Finite J] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem one_mem_tensorLogShellProductImage
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (1 : (j : J) → E j) ∈ tensorLogShellProductImage A e :=
  ⟨1, one_mem_tensorLogShellRegion A, e.map_one⟩

omit [Finite ι] [Finite J] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem unitRegion_subset_tensorLogShellHull
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    unitRegion (K := E) ⊆ hull (tensorLogShellProductImage A e) := by
  intro x hx lam _ hsub j
  have hnorm := hsub (one_mem_tensorLogShellProductImage A e) j
  exact (hx j).trans (by simpa only [Pi.one_apply, norm_one] using hnorm)

variable [∀ j, ProperSpace (E j)]

omit [Finite J] [∀ j, ProperSpace (E j)] in
theorem exists_tensorLogShellHull_eq_region
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    ∃ lam : (j : J) → E j, (∀ j, lam j ≠ 0) ∧
      hull (tensorLogShellProductImage A e) = region lam :=
  exists_hull_eq_region (isCompact_tensorLogShellProductImage A e)
    ⟨1, one_mem_tensorLogShellProductImage A e⟩
    (fun _ => ⟨1, one_mem_tensorLogShellProductImage A e, one_ne_zero⟩)

theorem isCompact_tensorLogShellHull
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (hull (tensorLogShellProductImage A e)) := by
  obtain ⟨lam, _, heq⟩ := exists_tensorLogShellHull_eq_region A e
  rw [heq]
  exact isCompact_region lam

theorem exists_integralModule_tensorLogShellHull [∀ j, IsUltrametricDist (E j)]
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    ∃ H : Submodule (integralRing (K := E)
        (fun j (x y : E j) => IsUltrametricDist.norm_add_le_max x y))
        ((j : J) → E j),
      (H : Set ((j : J) → E j)) = hull (tensorLogShellProductImage A e) ∧
        IsCompact (H : Set ((j : J) → E j)) :=
  exists_compact_integralModule_hull _ (isCompact_tensorLogShellProductImage A e).closure
    ⟨1, one_mem_tensorLogShellProductImage A e⟩
    (fun _ => ⟨1, one_mem_tensorLogShellProductImage A e, one_ne_zero⟩)

omit [∀ j, ProperSpace (E j)] in
theorem integralSpan_tensorLogShellProductImage_eq_hull [∀ j, IsUltrametricDist (E j)]
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (Submodule.span (integralRing (K := E)
      (fun j (x y : E j) => IsUltrametricDist.norm_add_le_max x y))
      (tensorLogShellProductImage A e) : Set ((j : J) → E j)) =
        hull (tensorLogShellProductImage A e) :=
  integralSpan_eq_hull _ (isCompact_tensorLogShellProductImage A e)
    ⟨1, one_mem_tensorLogShellProductImage A e⟩
    (fun _ => ⟨1, one_mem_tensorLogShellProductImage A e, one_ne_zero⟩)

section Haar

variable [MeasurableSpace ((j : J) → E j)]

theorem measure_tensorLogShellHull_pos_lt_top
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure ((j : J) → E j)) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] :
    0 < μ (hull (tensorLogShellProductImage A e)) ∧
      μ (hull (tensorLogShellProductImage A e)) < ⊤ :=
  measure_hull_pos_lt_top μ (isCompact_tensorLogShellProductImage A e).closure
    ⟨1, one_mem_tensorLogShellProductImage A e⟩
    (fun _ => ⟨1, one_mem_tensorLogShellProductImage A e, one_ne_zero⟩)

theorem measure_unitRegion_pos_lt_top
    (μ : Measure ((j : J) → E j)) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] :
    0 < μ (unitRegion (K := E)) ∧ μ (unitRegion (K := E)) < ⊤ := by
  have heq : unitRegion (K := E) = region (1 : (j : J) → E j) := by
    ext x
    simp only [unitRegion, region, Pi.one_apply, norm_one]
  rw [heq]
  exact ⟨measure_region_pos μ 1 (fun _ => one_ne_zero), measure_region_lt_top μ 1⟩

theorem tensorLogShellHull_logVolume_nonneg
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure ((j : J) → E j)) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] :
    0 ≤ normalizedLogVolume μ (hull (tensorLogShellProductImage A e)) := by
  have hle := normalizedLogVolume_mono μ (unitRegion_subset_tensorLogShellHull A e)
    (measure_unitRegion_pos_lt_top μ).1 (measure_tensorLogShellHull_pos_lt_top A e μ).2
  simpa only [normalizedLogVolume_unitRegion] using hle

end Haar

theorem addHaar_tensorLogShellHull_pos_lt_top
    (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    0 < Measure.addHaar (hull (tensorLogShellProductImage A e)) ∧
      Measure.addHaar (hull (tensorLogShellProductImage A e)) < ⊤ := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  exact measure_tensorLogShellHull_pos_lt_top A e Measure.addHaar

end

end LeanFormal.IUT.LocalFieldPadicTensor
