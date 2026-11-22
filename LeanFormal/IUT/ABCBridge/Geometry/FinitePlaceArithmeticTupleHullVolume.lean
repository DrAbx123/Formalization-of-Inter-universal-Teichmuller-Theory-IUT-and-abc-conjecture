import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullTransport

/-!
# A constructed unit-relative log-volume for each actual completion tensor block

Finite etale classification supplies a field-product decomposition. The proved
numerical transport theorem shows that all such decompositions compute the same
real number. The specification below has actual existence and uniqueness proofs
before its chosen value is used.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

def ArithmeticTupleHullUnitLogVolumeSpec (value : ℝ) : Prop :=
  ∀ (J : Type (max u v)) [Finite J] (E : J → Type (max u v))
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)),
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    normalizedLogVolume Measure.addHaar (hull (arithmeticTupleFieldLogImage places tuple e)) = value

theorem existsUnique_arithmeticTupleHullUnitLogVolume :
    ∃! value, ArithmeticTupleHullUnitLogVolumeSpec places tuple value := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  let value := normalizedLogVolume Measure.addHaar
    (hull (arithmeticTupleFieldLogImage places tuple e))
  refine ⟨value, ?_, ?_⟩
  · intro L hL F hfieldF halgebraF hfiniteF hproperF second
    letI := hL
    letI := hfieldF
    letI := halgebraF
    letI := hfiniteF
    letI := hproperF
    letI : MeasurableSpace ((l : L) → F l) := borel _
    letI : BorelSpace ((l : L) → F l) := ⟨rfl⟩
    exact arithmeticTupleFieldHull_addHaar_logVolume_decomposition_change places tuple e second
  · intro other hother
    exact (hother J E e).symm

def arithmeticTupleHullUnitLogVolume : ℝ :=
  Classical.choose (existsUnique_arithmeticTupleHullUnitLogVolume places tuple).exists

theorem arithmeticTupleHullUnitLogVolume_spec :
    ArithmeticTupleHullUnitLogVolumeSpec places tuple
      (arithmeticTupleHullUnitLogVolume places tuple) :=
  Classical.choose_spec (existsUnique_arithmeticTupleHullUnitLogVolume places tuple).exists

theorem arithmeticTupleHullUnitLogVolume_eq
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    arithmeticTupleHullUnitLogVolume places tuple =
      normalizedLogVolume Measure.addHaar (hull (arithmeticTupleFieldLogImage places tuple e)) :=
  ((arithmeticTupleHullUnitLogVolume_spec places tuple) J E e).symm

theorem arithmeticTupleHullUnitLogVolume_nonneg :
    0 ≤ arithmeticTupleHullUnitLogVolume places tuple := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  rw [arithmeticTupleHullUnitLogVolume_eq places tuple e]
  have hmono := normalizedLogVolume_mono Measure.addHaar
    (unitRegion_subset_arithmeticTupleFieldHull places tuple e)
    (measure_unitRegion_pos_lt_top Measure.addHaar).1
    (measure_arithmeticTupleFieldHull_pos_lt_top places tuple e Measure.addHaar).2
  simpa only [normalizedLogVolume_unitRegion] using hmono

end

end LeanFormal.IUT.NumberFieldFinitePlace
