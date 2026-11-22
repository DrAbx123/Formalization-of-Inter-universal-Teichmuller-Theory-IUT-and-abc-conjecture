import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullTransport

/-!
# Actual tuple-carrier hulls and unit references

Pull back the field-product hull and its integral unit region along a genuine
decomposition. Their sets on the original tuple tensor are independent of the
decomposition, by the proved topological ring transport of hulls and units.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull MeasureTheory

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type*} [Fintype ι] {V : ι → Type*}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable {J : Type*} [Finite J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]

def arithmeticTupleHullPullback
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Set (ArithmeticTensorTupleBlock places tuple) :=
  e.symm '' hull (arithmeticTupleFieldLogImage places tuple e)

def arithmeticTupleUnitReferencePullback
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    Set (ArithmeticTensorTupleBlock places tuple) := e.symm '' unitRegion (K := E)

variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

theorem isCompact_arithmeticTupleHullPullback
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (arithmeticTupleHullPullback places tuple e) :=
  (isCompact_arithmeticTupleFieldHull places tuple e).image
    e.symm.toLinearMap.continuous_of_finiteDimensional

theorem isCompact_arithmeticTupleUnitReferencePullback
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (arithmeticTupleUnitReferencePullback places tuple e) :=
  (isCompact_unitRegion (K := E)).image e.symm.toLinearMap.continuous_of_finiteDimensional

section Haar

variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

omit [Finite J] [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)] in
theorem measure_arithmeticTupleFieldPullback
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) (S : Set ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    μ (e.symm '' S) = (μ.map e.toLinearEquiv.toContinuousLinearEquiv) S := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  let equivalence := e.toLinearEquiv.toContinuousLinearEquiv
  change μ (e.symm '' S) = (μ.map equivalence.toHomeomorph.toMeasurableEquiv) S
  rw [MeasurableEquiv.map_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change e (e.symm y) ∈ S
    simpa only [AlgEquiv.apply_symm_apply] using hy
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩

omit [∀ j, FiniteDimensional ℚ_[p] (E j)] in
theorem measure_arithmeticTupleHullPullbacks_pos_lt_top
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    (0 < μ (arithmeticTupleHullPullback places tuple e) ∧
      μ (arithmeticTupleHullPullback places tuple e) < ⊤) ∧
    (0 < μ (arithmeticTupleUnitReferencePullback places tuple e) ∧
      μ (arithmeticTupleUnitReferencePullback places tuple e) < ⊤) := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  let equivalence := e.toLinearEquiv.toContinuousLinearEquiv
  let ν := μ.map equivalence
  letI : Measure.IsAddHaarMeasure ν := equivalence.toContinuousAddEquiv.isAddHaarMeasure_map μ
  constructor
  · unfold arithmeticTupleHullPullback
    rw [measure_arithmeticTupleFieldPullback]
    exact measure_arithmeticTupleFieldHull_pos_lt_top places tuple e ν
  · unfold arithmeticTupleUnitReferencePullback
    rw [measure_arithmeticTupleFieldPullback]
    exact measure_unitRegion_pos_lt_top ν

theorem arithmeticTupleHullPullback_relativeLogVolume
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    Real.log (μ (arithmeticTupleHullPullback places tuple e)).toReal -
      Real.log (μ (arithmeticTupleUnitReferencePullback places tuple e)).toReal =
      normalizedLogVolume Measure.addHaar (hull (arithmeticTupleFieldLogImage places tuple e)) := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  let equivalence := e.toLinearEquiv.toContinuousLinearEquiv.toContinuousAddEquiv
  have himage (S : Set ((j : J) → E j)) : e '' (e.symm '' S) = S := by
    simp only [Set.image_image, AlgEquiv.apply_symm_apply]
    exact Set.image_id S
  have hmass := measure_arithmeticTupleHullPullbacks_pos_lt_top places tuple e μ
  have hlog := NormalizedHaarTransport.relative_log_mass_image_eq equivalence μ Measure.addHaar
    (isCompact_arithmeticTupleHullPullback places tuple e).closure
    (isCompact_arithmeticTupleUnitReferencePullback places tuple e).closure hmass.1.1 hmass.2.1
  change Real.log (Measure.addHaar (e '' arithmeticTupleHullPullback places tuple e)).toReal -
    Real.log (Measure.addHaar (e '' arithmeticTupleUnitReferencePullback places tuple e)).toReal =
      _ at hlog
  simpa only [arithmeticTupleHullPullback, arithmeticTupleUnitReferencePullback, himage,
    normalizedLogVolume] using hlog.symm

end Haar

variable {L : Type*} [Finite L] {F : L → Type*}
variable [∀ l, NormedField (F l)] [∀ l, NormedAlgebra ℚ_[p] (F l)]
variable [∀ l, FiniteDimensional ℚ_[p] (F l)] [∀ l, ProperSpace (F l)]

omit [Fintype ι] in
theorem arithmeticTupleUnitReferencePullback_decomposition_change
    (first : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    arithmeticTupleUnitReferencePullback places tuple second =
      arithmeticTupleUnitReferencePullback places tuple first := by
  let changeField := first.symm.trans second
  have hunit := continuous_ringEquiv_image_unitRegion changeField.toRingEquiv
    changeField.toLinearMap.continuous_of_finiteDimensional
    changeField.symm.toLinearMap.continuous_of_finiteDimensional
  change changeField '' unitRegion (K := E) = unitRegion (K := F) at hunit
  unfold arithmeticTupleUnitReferencePullback
  rw [← hunit, Set.image_image]
  congr 1
  funext x
  exact second.symm_apply_apply (first.symm x)

omit [Fintype ι] in
theorem arithmeticTupleHullPullback_decomposition_change
    (first : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (second : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((l : L) → F l)) :
    arithmeticTupleHullPullback places tuple second =
      arithmeticTupleHullPullback places tuple first := by
  let changeField := first.symm.trans second
  have himage : changeField '' arithmeticTupleFieldLogImage places tuple first =
      arithmeticTupleFieldLogImage places tuple second := by
    simp only [arithmeticTupleFieldLogImage, Set.image_image, changeField,
      AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  have hhull := continuous_ringEquiv_image_hull changeField.toRingEquiv
    changeField.toLinearMap.continuous_of_finiteDimensional
    changeField.symm.toLinearMap.continuous_of_finiteDimensional
    (arithmeticTupleFieldLogImage places tuple first)
  change changeField '' hull (arithmeticTupleFieldLogImage places tuple first) =
    hull (changeField '' arithmeticTupleFieldLogImage places tuple first) at hhull
  rw [himage] at hhull
  unfold arithmeticTupleHullPullback
  rw [← hhull, Set.image_image]
  congr 1
  funext x
  exact second.symm_apply_apply (first.symm x)

end

end LeanFormal.IUT.NumberFieldFinitePlace
