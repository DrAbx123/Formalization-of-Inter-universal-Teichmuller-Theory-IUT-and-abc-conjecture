import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductLogVolumeTransport

/-!
# The actual arithmetic IQ hull and log-volume are independent of decomposition

The change of coordinates is the composite of two field-product algebra
equivalences of the constructed packet tensor. It sends the actual
log-shell image and its hull to those from the second decomposition.
The two canonical Haar measures give exactly the same unit-relative
log-volume; equality of sets alone is not used as a measure argument.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} {V : ι → Type*} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable {J L : Type*} {E : J → Type*} {F : L → Type*}
variable [∀ j, NormedField (E j)] [∀ l, NormedField (F l)]
variable [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ l, NormedAlgebra ℚ_[p] (F l)]

theorem arithmeticTensorProductImage_decomposition_change
    (first : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    (first.symm.trans second) '' arithmeticTensorProductImage places first =
      arithmeticTensorProductImage places second := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    change second x = second (first.symm (first x))
    rw [AlgEquiv.symm_apply_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨first x, ⟨x, hx, rfl⟩, ?_⟩
    change second (first.symm (first x)) = second x
    rw [AlgEquiv.symm_apply_apply]

variable [Finite J] [Finite L] [∀ j, FiniteDimensional ℚ_[p] (E j)]
variable [∀ l, FiniteDimensional ℚ_[p] (F l)]
variable [∀ j, ProperSpace (E j)] [∀ l, ProperSpace (F l)]

theorem arithmeticTensorHull_decomposition_change
    (first : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    (first.symm.trans second) '' hull (arithmeticTensorProductImage places first) =
      hull (arithmeticTensorProductImage places second) := by
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite L
  let changeOfDecomposition := first.symm.trans second
  have hforward : Continuous changeOfDecomposition :=
    changeOfDecomposition.toLinearMap.continuous_of_finiteDimensional
  have hbackward : Continuous changeOfDecomposition.symm :=
    changeOfDecomposition.symm.toLinearMap.continuous_of_finiteDimensional
  have htransport := continuous_ringEquiv_image_hull changeOfDecomposition.toRingEquiv
    hforward hbackward (arithmeticTensorProductImage places first)
  change changeOfDecomposition.toRingEquiv '' hull (arithmeticTensorProductImage places first) = _
  rw [htransport]
  change hull ((first.symm.trans second) '' arithmeticTensorProductImage places first) = _
  rw [arithmeticTensorProductImage_decomposition_change]

variable [Finite ι]

section Haar

variable [MeasurableSpace ((j : J) → E j)] [BorelSpace ((j : J) → E j)]
variable [MeasurableSpace ((l : L) → F l)] [BorelSpace ((l : L) → F l)]

theorem arithmeticTensorHull_logVolume_decomposition_change
    (first : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((l : L) → F l))
    (μ : Measure ((j : J) → E j)) (ν : Measure ((l : L) → F l))
    [Measure.IsAddHaarMeasure μ] [Measure.IsAddHaarMeasure ν] :
    normalizedLogVolume ν (hull (arithmeticTensorProductImage places second)) =
      normalizedLogVolume μ (hull (arithmeticTensorProductImage places first)) := by
  letI := Fintype.ofFinite J
  letI := Fintype.ofFinite L
  let changeOfDecomposition := first.symm.trans second
  have hforward : Continuous changeOfDecomposition :=
    changeOfDecomposition.toLinearMap.continuous_of_finiteDimensional
  have hbackward : Continuous changeOfDecomposition.symm :=
    changeOfDecomposition.symm.toLinearMap.continuous_of_finiteDimensional
  have htransport := normalizedLogVolume_hull_continuous_ringEquiv
    changeOfDecomposition.toRingEquiv hforward hbackward μ ν
    (isCompact_arithmeticTensorProductImage places first).closure
    ⟨1, one_mem_arithmeticTensorProductImage places first⟩
    (fun _ => ⟨1, one_mem_arithmeticTensorProductImage places first, one_ne_zero⟩)
  change normalizedLogVolume ν
    (hull ((first.symm.trans second) '' arithmeticTensorProductImage places first)) = _
    at htransport
  rw [arithmeticTensorProductImage_decomposition_change] at htransport
  exact htransport

end Haar

theorem arithmeticTensorHull_addHaar_logVolume_decomposition_change
    (first : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    letI : MeasurableSpace ((l : L) → F l) := borel _
    letI : BorelSpace ((l : L) → F l) := ⟨rfl⟩
    normalizedLogVolume (Measure.addHaar : Measure ((l : L) → F l))
      (hull (arithmeticTensorProductImage places second)) =
    normalizedLogVolume (Measure.addHaar : Measure ((j : J) → E j))
      (hull (arithmeticTensorProductImage places first)) := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  letI : MeasurableSpace ((l : L) → F l) := borel _
  letI : BorelSpace ((l : L) → F l) := ⟨rfl⟩
  exact arithmeticTensorHull_logVolume_decomposition_change places first second
    Measure.addHaar Measure.addHaar

end

end LeanFormal.IUT.NumberFieldFinitePlace
