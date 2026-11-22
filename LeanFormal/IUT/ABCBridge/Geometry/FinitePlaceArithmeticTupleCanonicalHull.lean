import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullPullback
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# The actual tuple tensor's decomposition-independent hull and unit reference

The pair is constructed from an existing finite etale decomposition. Every
other decomposition pulls its hull and unit region back to exactly these sets.
Existence and uniqueness precede the choice of the two actual regions.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

def ArithmeticTupleHullRegionsSpec
    (regions : Set (ArithmeticTensorTupleBlock places tuple) ×
      Set (ArithmeticTensorTupleBlock places tuple)) : Prop :=
  ∀ (J : Type (max u v)) [Finite J] (E : J → Type (max u v))
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)),
    regions.1 = arithmeticTupleHullPullback places tuple e ∧
      regions.2 = arithmeticTupleUnitReferencePullback places tuple e

theorem existsUnique_arithmeticTupleHullRegions :
    ∃! regions, ArithmeticTupleHullRegionsSpec places tuple regions := by
  letI := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  refine ⟨(arithmeticTupleHullPullback places tuple e,
    arithmeticTupleUnitReferencePullback places tuple e), ?_, ?_⟩
  · intro L hL F hfieldF halgebraF hfiniteF hproperF second
    letI := hL
    letI := hfieldF
    letI := halgebraF
    letI := hfiniteF
    letI := hproperF
    exact ⟨(arithmeticTupleHullPullback_decomposition_change places tuple e second).symm,
      (arithmeticTupleUnitReferencePullback_decomposition_change places tuple e second).symm⟩
  · intro other hother
    exact Prod.ext (hother J E e).1 (hother J E e).2

def arithmeticTupleHullRegions :=
  Classical.choose (existsUnique_arithmeticTupleHullRegions places tuple).exists

theorem arithmeticTupleHullRegions_spec :
    ArithmeticTupleHullRegionsSpec places tuple (arithmeticTupleHullRegions places tuple) :=
  Classical.choose_spec (existsUnique_arithmeticTupleHullRegions places tuple).exists

abbrev arithmeticTupleCanonicalHull := (arithmeticTupleHullRegions places tuple).1

abbrev arithmeticTupleCanonicalUnitReference := (arithmeticTupleHullRegions places tuple).2

theorem arithmeticTupleCanonicalHull_eq
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    arithmeticTupleCanonicalHull places tuple = arithmeticTupleHullPullback places tuple e :=
  (arithmeticTupleHullRegions_spec places tuple J E e).1

theorem arithmeticTupleCanonicalUnitReference_eq
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    arithmeticTupleCanonicalUnitReference places tuple =
      arithmeticTupleUnitReferencePullback places tuple e :=
  (arithmeticTupleHullRegions_spec places tuple J E e).2

section ActualTopology

variable [Fintype ι]

theorem isCompact_arithmeticTupleCanonicalRegions :
    IsCompact (arithmeticTupleCanonicalHull places tuple) ∧
      IsCompact (arithmeticTupleCanonicalUnitReference places tuple) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  rw [arithmeticTupleCanonicalHull_eq places tuple e,
    arithmeticTupleCanonicalUnitReference_eq places tuple e]
  exact ⟨isCompact_arithmeticTupleHullPullback places tuple e,
    isCompact_arithmeticTupleUnitReferencePullback places tuple e⟩

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

theorem measure_arithmeticTupleCanonicalRegions_pos_lt_top
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    (0 < μ (arithmeticTupleCanonicalHull places tuple) ∧
      μ (arithmeticTupleCanonicalHull places tuple) < ⊤) ∧
    (0 < μ (arithmeticTupleCanonicalUnitReference places tuple) ∧
      μ (arithmeticTupleCanonicalUnitReference places tuple) < ⊤) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  rw [arithmeticTupleCanonicalHull_eq places tuple e,
    arithmeticTupleCanonicalUnitReference_eq places tuple e]
  exact measure_arithmeticTupleHullPullbacks_pos_lt_top places tuple e μ

theorem arithmeticTupleCanonicalRegions_relativeLogVolume
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    Real.log (μ (arithmeticTupleCanonicalHull places tuple)).toReal -
      Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
      arithmeticTupleHullUnitLogVolume places tuple := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  rw [arithmeticTupleCanonicalHull_eq places tuple e,
    arithmeticTupleCanonicalUnitReference_eq places tuple e,
    arithmeticTupleHullPullback_relativeLogVolume]
  exact (arithmeticTupleHullUnitLogVolume_eq places tuple e).symm

end ActualTopology

end

end LeanFormal.IUT.NumberFieldFinitePlace
