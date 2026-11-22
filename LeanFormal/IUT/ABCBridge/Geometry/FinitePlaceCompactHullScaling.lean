import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Compactness-to-scaling for the finite-place arithmetic tuple hull

This file proves the analytic step of IUT III Corollary 3.12 used by the
`IQHullLogVolumeInterface` normalization: a compact subset of a finite product
of nonarchimedean local fields is contained in a nonzero scalar multiple of the
product unit region.  The scalar is obtained from the norm boundedness of a
compact set; no properness or finite-dimensional choice of basis is needed for
the scaling step itself.

The result is transported along the actual tensor-field decomposition of the
arithmetic tuple carrier.  Only the inclusion into a single scaled unit region
is asserted; no equality of the canonical hull with a scaled unit region is
claimed.
-/

open Metric MeasureTheory
open scoped Pointwise

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Finite ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-! ## General compactness-to-scaling lemmas -/

/-- A compact subset of a finite-dimensional normed `Q_p`-space is contained in
a nonzero scalar multiple of the closed unit ball.  The finite-dimensional
assumption is recorded for the consumer; the proof only uses norm boundedness
and the fact that `Q_p` has elements of arbitrarily large norm. -/
theorem compact_subset_smul_closedBall
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℚ_[p] W]
    [FiniteDimensional ℚ_[p] W]
    {T : Set W} (hT : IsCompact T) :
    ∃ lam : ℚ_[p], lam ≠ 0 ∧ T ⊆ lam • Metric.closedBall (0 : W) 1 := by
  have _hfinite : FiniteDimensional ℚ_[p] W := inferInstance
  obtain ⟨C, hC⟩ := hT.isBounded.subset_closedBall (0 : W)
  obtain ⟨lam, hlamC⟩ := NormedField.exists_lt_norm ℚ_[p] (max C (0 : ℝ))
  have hlampos : 0 < ‖lam‖ := (le_max_right C 0).trans_lt hlamC
  have hlam : lam ≠ 0 := norm_pos_iff.mp hlampos
  refine ⟨lam, hlam, ?_⟩
  intro x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam, Metric.mem_closedBall, dist_eq_norm,
    sub_zero, norm_smul, norm_inv]
  have hxle : ‖x‖ ≤ C := by
    have hx' : x ∈ Metric.closedBall (0 : W) C := hC hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
  have hlt : ‖lam‖⁻¹ * ‖x‖ < 1 := by
    calc
      ‖lam‖⁻¹ * ‖x‖ ≤ ‖lam‖⁻¹ * C :=
        mul_le_mul_of_nonneg_left hxle (inv_nonneg.mpr hlampos.le)
      _ < ‖lam‖⁻¹ * ‖lam‖ :=
        mul_lt_mul_of_pos_left ((le_max_left C 0).trans_lt hlamC) (inv_pos.mpr hlampos)
      _ = 1 := inv_mul_cancel₀ hlampos.ne'
  exact hlt.le

/-- A compact subset of a finite product of nonarchimedean local fields is
contained in a nonzero scalar multiple of the product unit region. -/
theorem compact_subset_smul_unitRegion
    {J : Type*} [Finite J] {E : J → Type*}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    {T : Set ((j : J) → E j)} (hT : IsCompact T) :
    ∃ lam : ℚ_[p], lam ≠ 0 ∧ T ⊆ lam • unitRegion (K := E) := by
  letI : Fintype J := Fintype.ofFinite J
  obtain ⟨C, hC⟩ := hT.isBounded.subset_closedBall (0 : (j : J) → E j)
  obtain ⟨lam, hlamC⟩ := NormedField.exists_lt_norm ℚ_[p] (max C (0 : ℝ))
  have hlampos : 0 < ‖lam‖ := (le_max_right C 0).trans_lt hlamC
  have hlam : lam ≠ 0 := norm_pos_iff.mp hlampos
  refine ⟨lam, hlam, ?_⟩
  intro x hx
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam]
  intro j
  rw [Pi.smul_apply, norm_smul, norm_inv]
  have hxj : ‖x j‖ ≤ ‖x‖ := norm_le_pi_norm x j
  have hxle : ‖x‖ ≤ C := by
    have hx' : x ∈ Metric.closedBall (0 : (j : J) → E j) C := hC hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx'
  have hlt : ‖lam‖⁻¹ * ‖x j‖ < 1 := by
    calc
      ‖lam‖⁻¹ * ‖x j‖ ≤ ‖lam‖⁻¹ * ‖x‖ :=
        mul_le_mul_of_nonneg_left hxj (inv_nonneg.mpr hlampos.le)
      _ ≤ ‖lam‖⁻¹ * C :=
        mul_le_mul_of_nonneg_left hxle (inv_nonneg.mpr hlampos.le)
      _ < ‖lam‖⁻¹ * ‖lam‖ :=
        mul_lt_mul_of_pos_left ((le_max_left C 0).trans_lt hlamC) (inv_pos.mpr hlampos)
      _ = 1 := inv_mul_cancel₀ hlampos.ne'
  exact hlt.le

/-- The scalar multiple of the product unit region is exactly the coordinate
disc region with constant radius `lam`.  This is the form in which the scalar is
absorbed into the integral reference region for the log-volume normalization. -/
theorem smul_unitRegion_eq_region
    {J : Type*} {E : J → Type*}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    (lam : ℚ_[p]) (hlam : lam ≠ 0) :
    lam • unitRegion (K := E) = region (fun j : J => algebraMap ℚ_[p] (E j) lam) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ j
    simpa only [Pi.smul_apply, norm_smul, norm_algebraMap'] using
      mul_le_of_le_one_right (norm_nonneg lam) (hy j)
  · intro hx
    have hne (j : J) : algebraMap ℚ_[p] (E j) lam ≠ 0 := by
      rw [← norm_pos_iff]
      simpa [norm_algebraMap'] using norm_pos_iff.mpr hlam
    refine ⟨fun j => (algebraMap ℚ_[p] (E j) lam)⁻¹ * x j, ?_, ?_⟩
    · intro j
      rw [norm_mul, norm_inv]
      have hpos : 0 < ‖algebraMap ℚ_[p] (E j) lam‖ := norm_pos_iff.mpr (hne j)
      calc
        ‖algebraMap ℚ_[p] (E j) lam‖⁻¹ * ‖x j‖ ≤
          ‖algebraMap ℚ_[p] (E j) lam‖⁻¹ * ‖algebraMap ℚ_[p] (E j) lam‖ :=
          mul_le_mul_of_nonneg_left (hx j) (inv_nonneg.mpr hpos.le)
        _ = 1 := inv_mul_cancel₀ hpos.ne'
    · funext j
      simp only [Pi.smul_apply, Algebra.smul_def]
      rw [← mul_assoc, mul_inv_cancel₀ (hne j), one_mul]

/-! ## Transport to the actual arithmetic tuple carrier -/

/-- Any compact subset of the actual tuple carrier is contained in a nonzero
scalar multiple of the canonical unit reference.  The proof uses one genuine
field-product decomposition and the general product scaling lemma. -/
theorem exists_smul_canonicalUnitReference_of_isCompact
    [Fintype ι]
    {T : Set (ArithmeticTensorTupleBlock places tuple)} (hT : IsCompact T) :
    ∃ lam : ℚ_[p], lam ≠ 0 ∧
      T ⊆ lam • arithmeticTupleCanonicalUnitReference places tuple := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI : Fintype J := Fintype.ofFinite J
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  have hT' : IsCompact (e '' T) :=
    hT.image e.toLinearMap.continuous_of_finiteDimensional
  obtain ⟨lam, hlam, hsub⟩ := compact_subset_smul_unitRegion (p := p) (E := E) hT'
  refine ⟨lam, hlam, ?_⟩
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
  intro x hx
  have hx' : e x ∈ lam • unitRegion (K := E) := hsub ⟨x, hx, rfl⟩
  rw [Set.mem_smul_set] at hx' ⊢
  obtain ⟨y, hy, hyx⟩ := hx'
  refine ⟨e.symm y, ⟨y, hy, rfl⟩, ?_⟩
  calc
    lam • e.symm y = e.symm (lam • y) := ((e.symm.toLinearEquiv).map_smul lam y).symm
    _ = e.symm (e x) := by rw [hyx]
    _ = x := e.symm_apply_apply x

/-- The canonical hull of the actual arithmetic tuple is contained in a nonzero
scalar multiple of the canonical unit reference.  This is the Corollary 3.12
compactness-to-scaled-unit-region step. -/
theorem arithmeticTupleCanonicalHull_subset_smul_unitReference :
    ∃ lam : ℚ_[p], lam ≠ 0 ∧
      arithmeticTupleCanonicalHull places tuple ⊆
        lam • arithmeticTupleCanonicalUnitReference places tuple := by
  letI : Fintype ι := Fintype.ofFinite ι
  exact exists_smul_canonicalUnitReference_of_isCompact places tuple
    (isCompact_arithmeticTupleCanonicalRegions places tuple).1

/-! ## Compactness, openness and Haar mass of the scaled reference -/

/-- The canonical unit reference is open: it is the pullback of the product
integer lattice, whose carrier is the product unit region. -/
theorem isOpen_arithmeticTupleCanonicalUnitReference [Fintype ι] :
    IsOpen (arithmeticTupleCanonicalUnitReference places tuple) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI : Fintype J := Fintype.ofFinite J
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  letI : ∀ j, CompleteSpace (E j) := fun j => (hE j).2.1
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
  unfold arithmeticTupleUnitReferencePullback
  have himage : e.symm '' unitRegion (K := E) = e ⁻¹' unitRegion (K := E) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  rw [himage]
  exact (isOpen_productIntegerLattice (p := p) (E := E)).preimage
    e.toLinearMap.continuous_of_finiteDimensional

/-- The canonical unit reference contains zero. -/
theorem zero_mem_arithmeticTupleCanonicalUnitReference :
    (0 : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleCanonicalUnitReference places tuple := by
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, _, _⟩ :=
    exists_arithmeticTensorTuple_fieldProduct places tuple
  letI := hJ
  letI : Fintype J := Fintype.ofFinite J
  letI := hfield
  letI := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
  exact ⟨0, by simp [unitRegion], by simp⟩

/-- A nonzero scalar multiple of the canonical unit reference is compact. -/
theorem isCompact_smul_arithmeticTupleCanonicalUnitReference
    [Fintype ι]
    (lam : ℚ_[p]) :
    IsCompact (lam • arithmeticTupleCanonicalUnitReference places tuple) := by
  exact (isCompact_arithmeticTupleCanonicalRegions places tuple).2.image
    (continuous_const_smul lam)

/-- A nonzero scalar multiple of the canonical unit reference is open. -/
theorem isOpen_smul_arithmeticTupleCanonicalUnitReference
    [Fintype ι]
    (lam : ℚ_[p]) (hlam : lam ≠ 0) :
    IsOpen (lam • arithmeticTupleCanonicalUnitReference places tuple) :=
  (isOpen_arithmeticTupleCanonicalUnitReference places tuple).smul₀ hlam

/-- A nonzero scalar multiple of the canonical unit reference contains zero. -/
theorem zero_mem_smul_arithmeticTupleCanonicalUnitReference
    (lam : ℚ_[p]) (hlam : lam ≠ 0) :
    (0 : ArithmeticTensorTupleBlock places tuple) ∈
      lam • arithmeticTupleCanonicalUnitReference places tuple := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hlam]
  simpa using zero_mem_arithmeticTupleCanonicalUnitReference places tuple

/-- A nonzero scalar multiple of the canonical unit reference has positive
finite Haar mass. -/
theorem measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top
    [Fintype ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (lam : ℚ_[p]) (hlam : lam ≠ 0) :
    0 < μ (lam • arithmeticTupleCanonicalUnitReference places tuple) ∧
      μ (lam • arithmeticTupleCanonicalUnitReference places tuple) < ⊤ := by
  constructor
  · exact (isOpen_smul_arithmeticTupleCanonicalUnitReference places tuple lam hlam).measure_pos μ
      ⟨0, zero_mem_smul_arithmeticTupleCanonicalUnitReference places tuple lam hlam⟩
  · exact (isCompact_smul_arithmeticTupleCanonicalUnitReference places tuple lam).measure_lt_top

/-- Absorbing the scalar into the integral reference: the scaled canonical unit
region is exactly the pullback of the coordinate disc region with constant
radius `lam`. -/
theorem smul_unitReference_absorbed_region
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (lam : ℚ_[p]) (hlam : lam ≠ 0) :
    lam • arithmeticTupleCanonicalUnitReference places tuple =
      e.symm '' region (fun j : J => algebraMap ℚ_[p] (E j) lam) := by
  rw [arithmeticTupleCanonicalUnitReference_eq places tuple e]
  unfold arithmeticTupleUnitReferencePullback
  rw [← image_smul_set e.symm lam (unitRegion (K := E)),
    smul_unitRegion_eq_region (p := p) (E := E) lam hlam]

/-- The canonical hull is contained in the pullback of the constant-radius
coordinate region, i.e. after absorbing the scalar into the unit reference. -/
theorem arithmeticTupleCanonicalHull_subset_pullback_region
    {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
    [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
    [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    ∃ lam : ℚ_[p], lam ≠ 0 ∧
      arithmeticTupleCanonicalHull places tuple ⊆
        e.symm '' region (fun j : J => algebraMap ℚ_[p] (E j) lam) := by
  obtain ⟨lam, hlam, hsub⟩ :=
    arithmeticTupleCanonicalHull_subset_smul_unitReference places tuple
  refine ⟨lam, hlam, ?_⟩
  rw [← smul_unitReference_absorbed_region places tuple e lam hlam]
  exact hsub

end

end LeanFormal.IUT.NumberFieldFinitePlace







