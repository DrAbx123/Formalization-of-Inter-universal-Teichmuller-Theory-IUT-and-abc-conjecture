import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegralTensorCovolume
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegerTensorLattice

/-!
# Comparison of the actual integer tensor with the integral log-shell

The actual `O_tensor` is the `Zp`-span of pure tensors of the local valuation
integer lattices. It is compact, open, and full rank. It is contained in the
actual integral log-shell tensor lattice, and it is contained in the canonical
holomorphic unit reference of every finite field-product decomposition.

The last containment lets us write the signed integral-log-tensor unit volume
as the difference of the two finite indices `I_tensor / O_tensor` and
`O_hol / O_tensor`. No equality between `O_tensor` and `O_hol` is assumed.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldLogarithm LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.CompactOpenAddSubgroup MeasureTheory
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

abbrev arithmeticTupleValuationIntegerLattice :
    Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  tensorIntegerLattice (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

abbrev ArithmeticTupleValuationIntegerTensor
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i) :=
  PiTensorProduct ℤ_[p] (fun i =>
    valuationIntegerLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

def arithmeticTupleValuationIntegerTensorToBlock :
    ArithmeticTupleValuationIntegerTensor places tuple →ₗ[ℤ_[p]]
      ArithmeticTensorTupleBlock places tuple :=
  integerTensorToPadicTensor (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem arithmeticTupleValuationIntegerTensorToBlock_injective :
    Function.Injective (arithmeticTupleValuationIntegerTensorToBlock places tuple) :=
  integerTensorToPadicTensor_injective (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem range_arithmeticTupleValuationIntegerTensorToBlock :
    LinearMap.range (arithmeticTupleValuationIntegerTensorToBlock places tuple) =
      arithmeticTupleValuationIntegerLattice places tuple :=
  range_integerTensorToPadicTensor (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

def arithmeticTupleValuationIntegerTensorEquivLattice :
    ArithmeticTupleValuationIntegerTensor places tuple ≃ₗ[ℤ_[p]]
      arithmeticTupleValuationIntegerLattice places tuple :=
  integerTensorEquivLattice (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

instance arithmeticTupleValuationIntegerLatticeFinite :
    Module.Finite ℤ_[p] (arithmeticTupleValuationIntegerLattice places tuple) :=
  tensorIntegerLatticeFinite (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

instance arithmeticTupleValuationIntegerLatticeFree :
    Module.Free ℤ_[p] (arithmeticTupleValuationIntegerLattice places tuple) :=
  tensorIntegerLatticeFree (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem isCompact_arithmeticTupleValuationIntegerLattice :
    IsCompact (arithmeticTupleValuationIntegerLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) :=
  isCompact_tensorIntegerLattice (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem isOpen_arithmeticTupleValuationIntegerLattice :
    IsOpen (arithmeticTupleValuationIntegerLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) :=
  isOpen_tensorIntegerLattice (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem span_padic_arithmeticTupleValuationIntegerLattice :
    Submodule.span ℚ_[p] (arithmeticTupleValuationIntegerLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) = ⊤ :=
  padic_span_tensorIntegerLattice_eq_top (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem finrank_arithmeticTupleValuationIntegerLattice :
    Module.finrank ℤ_[p] (arithmeticTupleValuationIntegerLattice places tuple) =
      Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) :=
  finrank_tensorIntegerLattice (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem arithmeticTupleValuationIntegerLattice_le_integralLogLattice :
    arithmeticTupleValuationIntegerLattice places tuple ≤
      arithmeticTupleIntegralLogLattice places tuple :=
  tensorIntegerLattice_le_logShellLattice (p := p)
    (A := fun i => CommonPrimeCompletion (places i (tuple i)))

theorem arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    [∀ j, IsUltrametricDist (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (arithmeticTupleValuationIntegerLattice places tuple :
      Set (ArithmeticTensorTupleBlock places tuple)) ⊆
        arithmeticTupleCanonicalUnitReference places tuple := by
  intro x hx
  have himage : e x ∈ unitRegion (K := E) := by
    have h := algHom_image_tensorIntegerLattice_subset_unitRegion (p := p)
      (A := fun i => CommonPrimeCompletion (places i (tuple i))) e.toAlgHom
    exact h ⟨x, hx, rfl⟩
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
  exact ⟨e x, himage, e.symm_apply_apply x⟩

theorem arithmeticTupleValuationIntegerLattice_toAddSubgroup_le_holomorphic
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    [∀ j, IsUltrametricDist (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup ≤
      arithmeticTupleHolomorphicIntegerSubgroup places tuple := by
  intro x hx
  have hx' : x ∈ arithmeticTupleCanonicalUnitReference places tuple :=
    arithmeticTupleValuationIntegerLattice_subset_canonicalUnitReference places tuple e hx
  have hspec := arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple
  change x ∈ (arithmeticTupleHolomorphicIntegerSubgroup places tuple :
    Set (ArithmeticTensorTupleBlock places tuple))
  rw [hspec.1]
  exact hx'

theorem intersectionIndex_eq_one_of_le
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {H K : AddSubgroup G} (h : H ≤ K) : intersectionIndex H K = 1 := by
  unfold intersectionIndex intersectionInLeft
  have htop : K.comap H.subtype = ⊤ := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_top, iff_true]
    exact h x.property
  rw [htop, ← AddSubgroup.index_eq_card, AddSubgroup.index_top]

def arithmeticTupleIntegerTensorLogShellIndex : ℕ :=
  intersectionIndex (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup
    (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup

def arithmeticTupleIntegerTensorHolomorphicIndex : ℕ :=
  intersectionIndex (arithmeticTupleHolomorphicIntegerSubgroup places tuple)
    (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup

def arithmeticTupleIntegerTensorSignedLogVolume : ℝ :=
  Real.log (arithmeticTupleIntegerTensorLogShellIndex places tuple : ℝ) -
    Real.log (arithmeticTupleIntegerTensorHolomorphicIndex places tuple : ℝ)

theorem arithmeticTupleIntegerTensorSignedLogVolume_eq_logTensorUnitLogVolume
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    [∀ j, IsUltrametricDist (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleIntegerTensorSignedLogVolume places tuple =
      arithmeticTupleLogTensorUnitLogVolume places tuple := by
  have hIO := relative_log_measure_eq_log_indices
    (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup
    (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup
    (isCompact_arithmeticTupleIntegralLogLattice places tuple)
    (isCompact_arithmeticTupleValuationIntegerLattice places tuple)
    (isOpen_arithmeticTupleIntegralLogLattice places tuple)
    (isOpen_arithmeticTupleValuationIntegerLattice places tuple) μ
  have hKO := relative_log_measure_eq_log_indices
    (arithmeticTupleHolomorphicIntegerSubgroup places tuple)
    (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup
    (arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple).2.1
    (isCompact_arithmeticTupleValuationIntegerLattice places tuple)
    (arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple).2.2
    (isOpen_arithmeticTupleValuationIntegerLattice places tuple) μ
  have hIK := relative_log_measure_eq_log_indices
    (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup
    (arithmeticTupleHolomorphicIntegerSubgroup places tuple)
    (isCompact_arithmeticTupleIntegralLogLattice places tuple)
    (arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple).2.1
    (isOpen_arithmeticTupleIntegralLogLattice places tuple)
    (arithmeticTupleHolomorphicIntegerSubgroup_spec places tuple).2.2 μ
  have hOI : intersectionIndex
      (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup
      (arithmeticTupleIntegralLogLattice places tuple).toAddSubgroup = 1 :=
    intersectionIndex_eq_one_of_le
      (arithmeticTupleValuationIntegerLattice_le_integralLogLattice places tuple)
  have hOK : intersectionIndex
      (arithmeticTupleValuationIntegerLattice places tuple).toAddSubgroup
      (arithmeticTupleHolomorphicIntegerSubgroup places tuple) = 1 :=
    intersectionIndex_eq_one_of_le
      (arithmeticTupleValuationIntegerLattice_toAddSubgroup_le_holomorphic places tuple e)
  rw [hOI] at hIO
  rw [hOK] at hKO
  simp only [Nat.cast_one, Real.log_one, sub_zero] at hIO hKO
  unfold arithmeticTupleIntegerTensorSignedLogVolume
    arithmeticTupleIntegerTensorLogShellIndex
    arithmeticTupleIntegerTensorHolomorphicIndex
    arithmeticTupleLogTensorUnitLogVolume
    arithmeticTupleLogTensorIntersectionIndex
    arithmeticTupleHolomorphicIntersectionIndex
  linarith

end

end LeanFormal.IUT.NumberFieldFinitePlace
