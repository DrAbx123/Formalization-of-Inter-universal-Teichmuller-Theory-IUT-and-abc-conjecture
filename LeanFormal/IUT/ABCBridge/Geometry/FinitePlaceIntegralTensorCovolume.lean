import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralLogTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import LeanFormal.IUT.Foundations.MeasureTheory.CompactOpenAddSubgroupIndex

/-!
# The actual integral log-tensor covolume relative to holomorphic integers

The existing decomposition-independent integer reference is realized as
a compact open additive subgroup. The two actual finite intersection
indices then compute the signed relative Haar logarithm of the integral
log-tensor lattice. Neither equality nor containment of the two integral
structures is assumed.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull LeanFormal.IUT.CompactOpenAddSubgroup MeasureTheory
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

theorem exists_arithmeticTupleHolomorphicIntegerSubgroup :
    ∃ H : AddSubgroup (ArithmeticTensorTupleBlock places tuple),
      (H : Set (ArithmeticTensorTupleBlock places tuple)) =
        arithmeticTupleCanonicalUnitReference places tuple ∧
      IsCompact (H : Set (ArithmeticTensorTupleBlock places tuple)) ∧
        IsOpen (H : Set (ArithmeticTensorTupleBlock places tuple)) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  let H := (productIntegerLattice (p := p) (E := E)).toAddSubgroup.comap
    e.toLinearMap.toAddMonoidHom
  have hset : (H : Set (ArithmeticTensorTupleBlock places tuple)) =
      arithmeticTupleCanonicalUnitReference places tuple := by
    rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
    ext x
    change e x ∈ unitRegion (K := E) ↔ x ∈ e.symm '' unitRegion (K := E)
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [AlgEquiv.apply_symm_apply] using hy
  refine ⟨H, hset, ?_, ?_⟩
  · rw [hset]
    exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2
  · exact (isOpen_productIntegerLattice (p := p) (E := E)).preimage
      e.toLinearMap.continuous_of_finiteDimensional

def arithmeticTupleHolomorphicIntegerSubgroup :
    AddSubgroup (ArithmeticTensorTupleBlock places tuple) :=
  Classical.choose (exists_arithmeticTupleHolomorphicIntegerSubgroup places tuple)

theorem arithmeticTupleHolomorphicIntegerSubgroup_spec :
    (arithmeticTupleHolomorphicIntegerSubgroup places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) =
      arithmeticTupleCanonicalUnitReference places tuple ∧
      IsCompact (arithmeticTupleHolomorphicIntegerSubgroup places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) ∧
      IsOpen (arithmeticTupleHolomorphicIntegerSubgroup places tuple :
        Set (ArithmeticTensorTupleBlock places tuple)) :=
  Classical.choose_spec (exists_arithmeticTupleHolomorphicIntegerSubgroup places tuple)

def arithmeticTupleLogTensorIntersectionIndex : ℕ :=
  intersectionIndex (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup
    (arithmeticTupleHolomorphicIntegerSubgroup places tuple)

def arithmeticTupleHolomorphicIntersectionIndex : ℕ :=
  intersectionIndex (arithmeticTupleHolomorphicIntegerSubgroup places tuple)
    (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup

theorem arithmeticTupleIntersectionIndices_pos :
    0 < arithmeticTupleLogTensorIntersectionIndex places tuple ∧
      0 < arithmeticTupleHolomorphicIntersectionIndex places tuple := by
  have hreference := arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple
  exact ⟨intersectionIndex_pos _ _ (isCompact_arithmeticTupleIntegralLogLattice places tuple)
      hreference.2.2,
    intersectionIndex_pos _ _ hreference.2.1
      (isOpen_arithmeticTupleIntegralLogLattice places tuple)⟩

def arithmeticTupleLogTensorUnitLogVolume : ℝ :=
  Real.log (arithmeticTupleLogTensorIntersectionIndex places tuple : ℝ) -
    Real.log (arithmeticTupleHolomorphicIntersectionIndex places tuple : ℝ)

theorem arithmeticTupleIntegralLogLattice_subset_canonicalHull :
    (arithmeticTupleIntegralLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) ⊆
        arithmeticTupleCanonicalHull places tuple := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  let integralMap : ArithmeticTensorTupleBlock places tuple →ₗ[ℤ_[p]] ((j : J) → E j) := {
    toFun := e
    map_add' := e.map_add
    map_smul' := fun z x => by
      change e ((z : ℚ_[p]) • x) = (z : ℚ_[p]) • e x
      exact e.toLinearMap.map_smul _ _ }
  let pulledHull := (productHullLattice (p := p)
    (arithmeticTupleFieldLogImage places tuple e)).comap integralMap
  have hspan : arithmeticTupleIntegralLogLattice places tuple ≤ pulledHull := by
    apply Submodule.span_le.mpr
    intro x hx
    change e x ∈ hull (arithmeticTupleFieldLogImage places tuple e)
    exact subset_hull _ ⟨x, hx, rfl⟩
  intro x hx
  rw [arithmeticTupleCanonicalHull_eq places tuple e]
  exact ⟨e x, hspan hx, e.symm_apply_apply x⟩

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

theorem arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleLogTensorUnitLogVolume places tuple =
      Real.log (μ (arithmeticTupleIntegralLogLattice places tuple :
        Set (ArithmeticTensorTupleBlock places tuple))).toReal -
        Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal := by
  have hreference := arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple
  have hlog := relative_log_measure_eq_log_indices
    (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup
    (arithmeticTupleHolomorphicIntegerSubgroup places tuple)
    (isCompact_arithmeticTupleIntegralLogLattice places tuple) hreference.2.1
    (isOpen_arithmeticTupleIntegralLogLattice places tuple) hreference.2.2 μ
  rw [hreference.1] at hlog
  exact hlog.symm

theorem arithmeticTupleLogTensorUnitLogVolume_le_hull
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleLogTensorUnitLogVolume places tuple ≤
      arithmeticTupleHullUnitLogVolume places tuple := by
  have hlattice := measure_arithmeticTupleIntegralLogLattice_pos_lt_top places tuple μ
  have hhull := (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1
  have hlog := Real.log_le_log
    (ENNReal.toReal_pos hlattice.1.ne' hlattice.2.ne)
    (ENNReal.toReal_mono hhull.2.ne (measure_mono
      (arithmeticTupleIntegralLogLattice_subset_canonicalHull places tuple)))
  rw [arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog places tuple μ,
    ← arithmeticTupleCanonicalRegions_relativeLogVolume places tuple μ]
  exact sub_le_sub_right hlog _

theorem arithmeticTupleLogTensorUnitLogVolume_eq_fieldLogVolume
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    [MeasurableSpace ((j : J) → E j)] [BorelSpace ((j : J) → E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (ν : Measure ((j : J) → E j)) [Measure.IsAddHaarMeasure ν] :
    arithmeticTupleLogTensorUnitLogVolume places tuple = normalizedLogVolume ν
      (e '' (arithmeticTupleIntegralLogLattice places tuple :
        Set (ArithmeticTensorTupleBlock places tuple))) := by
  have hunit : e '' arithmeticTupleCanonicalUnitReference places tuple = unitRegion := by
    rw [arithmeticTupleCanonicalUnitReference_eq places tuple e,
      arithmeticTupleUnitReferencePullback, Set.image_image]
    simp only [AlgEquiv.apply_symm_apply, Set.image_id']
  have hrelative := NormalizedHaarTransport.relative_log_mass_image_eq
    e.toLinearEquiv.toContinuousLinearEquiv.toContinuousAddEquiv μ ν
    (isCompact_arithmeticTupleIntegralLogLattice places tuple).closure
    (isCompact_arithmeticTupleCanonicalRegions places tuple).2.closure
    (measure_arithmeticTupleIntegralLogLattice_pos_lt_top places tuple μ).1
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).2.1
  change Real.log (ν (e '' (arithmeticTupleIntegralLogLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)))).toReal -
    Real.log (ν (e '' arithmeticTupleCanonicalUnitReference places tuple)).toReal = _
    at hrelative
  rw [hunit] at hrelative
  rw [arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog places tuple μ]
  exact hrelative.symm

end

end LeanFormal.IUT.NumberFieldFinitePlace
