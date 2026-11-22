import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQTensor
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHullSpan

/-!
# Constructed product-field hull of the arithmetic tensor integral region

The input is the actual packet of completion log-shells. Finite etale
classification constructs a field-product decomposition; compactness and
the tensor identity then give its least integral hull and positive finite
canonical Haar mass. Positive mass is asserted for this hull, not for the
pure-tensor image itself.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable {J : Type*} [Finite J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]

def arithmeticTensorProductImage
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) : Set ((j : J) → E j) :=
  e '' arithmeticTensorLogRegion places

omit [Finite J] in
theorem isCompact_arithmeticTensorProductImage
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (arithmeticTensorProductImage places e) := by
  letI := Fintype.ofFinite ι
  exact (isCompact_arithmeticTensorLogRegion places).image
    e.toLinearMap.continuous_of_finiteDimensional

omit [Finite ι] [Finite J] in
theorem one_mem_arithmeticTensorProductImage
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (1 : (j : J) → E j) ∈ arithmeticTensorProductImage places e :=
  ⟨1, one_mem_arithmeticTensorLogRegion places, e.map_one⟩

omit [Finite J] in
theorem exists_arithmeticTensorHull_eq_region
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    ∃ lam : (j : J) → E j, (∀ j, lam j ≠ 0) ∧
      hull (arithmeticTensorProductImage places e) = region lam :=
  exists_hull_eq_region (isCompact_arithmeticTensorProductImage places e)
    ⟨1, one_mem_arithmeticTensorProductImage places e⟩
    (fun _ => ⟨1, one_mem_arithmeticTensorProductImage places e, one_ne_zero⟩)

theorem integralSpan_arithmeticTensorProductImage_eq_hull [∀ j, IsUltrametricDist (E j)]
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (Submodule.span (integralRing (K := E)
      (fun j (x y : E j) => IsUltrametricDist.norm_add_le_max x y))
      (arithmeticTensorProductImage places e) : Set ((j : J) → E j)) =
        hull (arithmeticTensorProductImage places e) :=
  integralSpan_eq_hull _ (isCompact_arithmeticTensorProductImage places e)
    ⟨1, one_mem_arithmeticTensorProductImage places e⟩
    (fun _ => ⟨1, one_mem_arithmeticTensorProductImage places e, one_ne_zero⟩)

variable [∀ j, ProperSpace (E j)]

theorem isCompact_arithmeticTensorHull
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (hull (arithmeticTensorProductImage places e)) := by
  obtain ⟨lam, _, heq⟩ := exists_arithmeticTensorHull_eq_region places e
  rw [heq]
  exact isCompact_region lam

theorem addHaar_arithmeticTensorHull_pos_lt_top
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    0 < Measure.addHaar (hull (arithmeticTensorProductImage places e)) ∧
      Measure.addHaar (hull (arithmeticTensorProductImage places e)) < ⊤ := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  exact measure_hull_pos_lt_top Measure.addHaar
    (isCompact_arithmeticTensorProductImage places e).closure
    ⟨1, one_mem_arithmeticTensorProductImage places e⟩
    (fun _ => ⟨1, one_mem_arithmeticTensorProductImage places e, one_ne_zero⟩)

theorem exists_realized_arithmeticTensorHull :
    ∃ (J : Type (max u (max v w))) (_ : Fintype J) (E : J → Type (max u (max v w)))
      (_ : ∀ j, NontriviallyNormedField (E j)) (_ : ∀ j, NormedAlgebra ℚ_[p] (E j))
      (_ : ∀ j, FiniteDimensional ℚ_[p] (E j)) (_ : ∀ j, ProperSpace (E j))
      (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) (lam : (j : J) → E j),
      (∀ j, FiniteDimensional ℚ_[p] (E j) ∧ CompleteSpace (E j) ∧ IsUltrametricDist (E j)) ∧
      (∀ j, lam j ≠ 0) ∧ hull (arithmeticTensorProductImage places e) = region lam ∧
      IsCompact (hull (arithmeticTensorProductImage places e)) ∧
      (letI : MeasurableSpace ((j : J) → E j) := borel _
       letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
       0 < Measure.addHaar (hull (arithmeticTensorProductImage places e)) ∧
         Measure.addHaar (hull (arithmeticTensorProductImage places e)) < ⊤) := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hnorm, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticPacketTensor_fieldProduct places
  letI := hJ
  letI := hnorm
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  obtain ⟨lam, hlam, heq⟩ := exists_arithmeticTensorHull_eq_region places e
  exact ⟨J, hJ, E, hnorm, halgebra, inferInstance, inferInstance, e, lam, hE, hlam, heq,
    isCompact_arithmeticTensorHull places e, addHaar_arithmeticTensorHull_pos_lt_top places e⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace
