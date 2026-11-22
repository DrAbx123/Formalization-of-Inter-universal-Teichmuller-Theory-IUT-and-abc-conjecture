import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlockFields
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductLogVolumeTransport

/-!
# Unit-relative Haar hull volume under actual tuple-field decomposition changes

Both decompositions apply to the same completion tensor and the same compact
log-shell tensor region. Their composite is a continuous Qp-algebra equivalence.
The proved field-product hull and numerical Haar transport theorems therefore
compare their actual unit-relative logarithmic masses.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Finite ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable {J : Type*} [Finite J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]

def arithmeticTupleFieldLogImage
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Set ((j : J) → E j) := e '' arithmeticTensorTupleLogRegion places tuple

omit [Finite J] in
theorem isCompact_arithmeticTupleFieldLogImage
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (arithmeticTupleFieldLogImage places tuple e) := by
  letI := Fintype.ofFinite ι
  exact (isCompact_arithmeticTensorTupleLogRegion places tuple).image
    e.toLinearMap.continuous_of_finiteDimensional

omit [Finite ι] [Finite J] in
theorem one_mem_arithmeticTupleFieldLogImage
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (1 : (j : J) → E j) ∈ arithmeticTupleFieldLogImage places tuple e :=
  ⟨1, one_mem_arithmeticTensorTupleLogRegion places tuple, e.map_one⟩

omit [Finite ι] [Finite J] in
theorem unitRegion_subset_arithmeticTupleFieldHull
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    unitRegion (K := E) ⊆ hull (arithmeticTupleFieldLogImage places tuple e) := by
  intro x hx lam _ hsub j
  have hone := hsub (one_mem_arithmeticTupleFieldLogImage places tuple e) j
  exact (hx j).trans (by simpa only [Pi.one_apply, norm_one] using hone)

variable [∀ j, ProperSpace (E j)]

theorem isCompact_arithmeticTupleFieldHull
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (hull (arithmeticTupleFieldLogImage places tuple e)) := by
  obtain ⟨lam, _, heq⟩ := exists_hull_eq_region
    (isCompact_arithmeticTupleFieldLogImage places tuple e)
    ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple e⟩
    (fun _ => ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple e, one_ne_zero⟩)
  rw [heq]
  exact isCompact_region lam

theorem measure_arithmeticTupleFieldHull_pos_lt_top
    [MeasurableSpace ((j : J) → E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure ((j : J) → E j)) [Measure.IsAddHaarMeasure μ] :
    0 < μ (hull (arithmeticTupleFieldLogImage places tuple e)) ∧
      μ (hull (arithmeticTupleFieldLogImage places tuple e)) < ⊤ :=
  measure_hull_pos_lt_top μ (isCompact_arithmeticTupleFieldLogImage places tuple e).closure
    ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple e⟩
    (fun _ => ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple e, one_ne_zero⟩)

variable [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable {L : Type*} [Finite L] {F : L → Type*}
variable [∀ l, NormedField (F l)] [∀ l, NormedAlgebra ℚ_[p] (F l)]
variable [∀ l, FiniteDimensional ℚ_[p] (F l)] [∀ l, ProperSpace (F l)]

theorem arithmeticTupleFieldHull_addHaar_logVolume_decomposition_change
    [MeasurableSpace ((j : J) → E j)] [BorelSpace ((j : J) → E j)]
    [MeasurableSpace ((l : L) → F l)] [BorelSpace ((l : L) → F l)]
    (first : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    normalizedLogVolume Measure.addHaar (hull (arithmeticTupleFieldLogImage places tuple second)) =
      normalizedLogVolume Measure.addHaar
        (hull (arithmeticTupleFieldLogImage places tuple first)) := by
  let changeField := first.symm.trans second
  have himage : changeField '' arithmeticTupleFieldLogImage places tuple first =
      arithmeticTupleFieldLogImage places tuple second := by
    simp only [arithmeticTupleFieldLogImage, Set.image_image, changeField,
      AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [← himage]
  exact addHaar_normalizedLogVolume_hull_continuous_ringEquiv changeField.toRingEquiv
    changeField.toLinearMap.continuous_of_finiteDimensional
    changeField.symm.toLinearMap.continuous_of_finiteDimensional
    (isCompact_arithmeticTupleFieldLogImage places tuple first).closure
    ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple first⟩
    (fun _ => ⟨1, one_mem_arithmeticTupleFieldLogImage places tuple first, one_ne_zero⟩)

end

end LeanFormal.IUT.NumberFieldFinitePlace
