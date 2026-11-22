import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQHullTransport

/-!
# A constructed, decomposition-independent arithmetic hull log-mass

Existence is supplied by the proved finite-etale decomposition, and
uniqueness by numerical Haar transport. The chosen real is therefore an
actual value computed by every such decomposition. It is relative to the
unit region. The additional packet normalization of III Proposition 3.9(i)
and the Gaussian regions are separate mathematical requirements.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)

def ArithmeticTensorHullUnitLogVolumeSpec (value : ℝ) : Prop :=
  ∀ (J : Type (max u (max v w))) [Fintype J] (E : J → Type (max u (max v w)))
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)),
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    normalizedLogVolume Measure.addHaar (hull (arithmeticTensorProductImage places e)) = value

theorem existsUnique_arithmeticTensorHullUnitLogVolume :
    ∃! value, ArithmeticTensorHullUnitLogVolumeSpec places value := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hnorm, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticPacketTensor_fieldProduct places
  letI := hJ
  letI := hnorm
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  let value := normalizedLogVolume Measure.addHaar (hull (arithmeticTensorProductImage places e))
  refine ⟨value, ?_, ?_⟩
  · intro L hL F hnormF halgebraF hfiniteF hproperF second
    letI := hL
    letI := hnormF
    letI := halgebraF
    letI := hfiniteF
    letI := hproperF
    exact arithmeticTensorHull_addHaar_logVolume_decomposition_change places e second
  · intro other hother
    exact (hother J E e).symm

def arithmeticTensorHullUnitLogVolume : ℝ :=
  Classical.choose (existsUnique_arithmeticTensorHullUnitLogVolume places).exists

theorem arithmeticTensorHullUnitLogVolume_spec :
    ArithmeticTensorHullUnitLogVolumeSpec places (arithmeticTensorHullUnitLogVolume places) :=
  Classical.choose_spec (existsUnique_arithmeticTensorHullUnitLogVolume places).exists

theorem arithmeticTensorHullUnitLogVolume_eq
    {J : Type (max u (max v w))} [Finite J] {E : J → Type (max u (max v w))}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticPacketTensor places ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    arithmeticTensorHullUnitLogVolume places =
      normalizedLogVolume Measure.addHaar (hull (arithmeticTensorProductImage places e)) := by
  letI := Fintype.ofFinite J
  exact ((arithmeticTensorHullUnitLogVolume_spec places) J E e).symm

theorem arithmeticTensorHullUnitLogVolume_nonneg :
    0 ≤ arithmeticTensorHullUnitLogVolume places := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hnorm, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticPacketTensor_fieldProduct places
  letI := hJ
  letI := hnorm
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  rw [arithmeticTensorHullUnitLogVolume_eq places e]
  have hsub : unitRegion (K := E) ⊆ hull (arithmeticTensorProductImage places e) := by
    intro x hx lam _ hcontains j
    have hone := hcontains (one_mem_arithmeticTensorProductImage places e) j
    exact (hx j).trans (by simpa only [Pi.one_apply, norm_one] using hone)
  have hmono := normalizedLogVolume_mono Measure.addHaar hsub
    (measure_unitRegion_pos_lt_top Measure.addHaar).1
    (addHaar_arithmeticTensorHull_pos_lt_top places e).2
  simpa only [normalizedLogVolume_unitRegion] using hmono

end

end LeanFormal.IUT.NumberFieldFinitePlace
