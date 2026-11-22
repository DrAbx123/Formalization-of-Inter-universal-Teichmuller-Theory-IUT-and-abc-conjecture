import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellHull

/-!
# A constructed field-product realization of the finite log-shell hull

The decomposition, its finite normed output fields, the nonzero hull
scales, compactness and the actual Haar mass are all supplied by proved
constructions. No source decomposition or hull witness is a premise.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Finite ι]
variable (A : ι → Type) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]

theorem exists_realized_tensorLogShell_hull :
    ∃ (J : Type) (_ : Fintype J) (E : J → Type)
      (_ : ∀ j, NontriviallyNormedField (E j)) (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (_ : ∀ j, FiniteDimensional ℚ_[p] (E j)) (_ : ∀ j, ProperSpace (E j))
      (_ : ∀ j, IsUltrametricDist (E j))
      (e : FinitePadicTensor (p := p) A ≃ₐ[ℚ_[p]] ((j : J) → E j))
      (lam : (j : J) → E j),
      (∀ j, lam j ≠ 0) ∧ hull (tensorLogShellProductImage A e) = region lam ∧
      IsCompact (hull (tensorLogShellProductImage A e)) ∧
      unitRegion (K := E) ⊆ hull (tensorLogShellProductImage A e) ∧
      (letI : MeasurableSpace ((j : J) → E j) := borel _
       letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
       0 < Measure.addHaar (unitRegion (K := E)) ∧
       Measure.addHaar (unitRegion (K := E)) < ⊤ ∧
       0 < Measure.addHaar (hull (tensorLogShellProductImage A e)) ∧
       Measure.addHaar (hull (tensorLogShellProductImage A e)) < ⊤ ∧
       normalizedLogVolume Measure.addHaar (unitRegion (K := E)) = 0 ∧
       0 ≤ normalizedLogVolume Measure.addHaar (hull (tensorLogShellProductImage A e))) := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_finiteNormedFieldProduct_piTensor (p := p) A
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  obtain ⟨lam, hlam, hhull⟩ := exists_tensorLogShellHull_eq_region A e
  refine ⟨J, inferInstance, E, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e, lam, hlam, hhull, isCompact_tensorLogShellHull A e,
    unitRegion_subset_tensorLogShellHull A e, ?_⟩
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  have hunit := measure_unitRegion_pos_lt_top (E := E) Measure.addHaar
  have hlog := measure_tensorLogShellHull_pos_lt_top A e Measure.addHaar
  exact ⟨hunit.1, hunit.2, hlog.1, hlog.2, normalizedLogVolume_unitRegion _,
    tensorLogShellHull_logVolume_nonneg A e Measure.addHaar⟩

end

end LeanFormal.IUT.LocalFieldPadicTensor
