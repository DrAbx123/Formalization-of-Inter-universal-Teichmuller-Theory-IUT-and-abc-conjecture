import LeanFormal.IUT.Foundations.LocalFields.DifferentTraceProduct
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Trace pairing under extension of scalars

This supplies the trace-lattice algebra needed for global/local different
compatibility. The target tensor algebra need not be a field. No completion
decomposition or identification is postulated.
-/

namespace LeanFormal.IUT.DifferentTraceBaseChange

open scoped TensorProduct BigOperators Pointwise

section InverseLattices

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- An inverse pair of order-stable lattices determines the actual ideal
quotient, even when the ambient algebra has zero divisors. -/
theorem lattice_eq_quotient_of_inverse
    (order different codifferent : Submodule R A)
    (contains_one : 1 ≤ order) (stable : order * different ≤ different)
    (inverse : different * codifferent = order) :
    different = order / codifferent := by
  apply le_antisymm
  · exact Submodule.le_div_iff_mul_le.mpr inverse.le
  · have quotient_mul : (order / codifferent) * codifferent ≤ order :=
      Submodule.le_div_iff_mul_le.mp le_rfl
    calc
      order / codifferent = (order / codifferent) * 1 := (mul_one _).symm
      _ ≤ (order / codifferent) * order := mul_le_mul_right contains_one _
      _ = (order / codifferent) * (codifferent * different) := by
        rw [mul_comm codifferent different, inverse]
      _ = ((order / codifferent) * codifferent) * different := (mul_assoc _ _ _).symm
      _ ≤ order * different := mul_le_mul_left quotient_mul _
      _ ≤ different := stable

end InverseLattices

section Trace

variable (K F A : Type*) [Field K] [CommRing F] [CommRing A]
  [Algebra K F] [Algebra K A] [FiniteDimensional K A]

/-- Scalar extension of an element preserves its trace by scalar extension. -/
theorem trace_one_tmul (x : A) :
    Algebra.trace F (F ⊗[K] A) (1 ⊗ₜ[K] x) =
      algebraMap K F (Algebra.trace K A x) := by
  classical
  let basis := Module.Free.chooseBasis K A
  rw [Algebra.trace_eq_matrix_trace (basis.baseChange F),
    Algebra.trace_eq_matrix_trace basis]
  simp [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Module.Basis.baseChange_apply, Module.Basis.baseChange_repr_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def, map_sum]

end Trace

section DualBases

variable (R K M : Type*) [CommRing R] [Field K] [AddCommGroup M]
  [Algebra R K] [Module R M] [Module K M] [IsScalarTower R K M]
  {ι : Type*} [Finite ι] [DecidableEq ι]

/-- A pair of actual dual bases determines the integral dual lattice. -/
theorem dualSubmodule_span_of_dualBases
    (pairing : LinearMap.BilinForm K M) (basis dualBasis : Module.Basis ι K M)
    (dual : ∀ i j, pairing (dualBasis i) (basis j) = if i = j then 1 else 0) :
    pairing.dualSubmodule (Submodule.span R (Set.range basis)) =
      Submodule.span R (Set.range dualBasis) := by
  classical
  letI := Fintype.ofFinite ι
  apply le_antisymm
  · intro x hx
    have coordinates (i : ι) : pairing x (basis i) = dualBasis.repr x i := by
      conv_lhs => rw [← dualBasis.sum_repr x]
      change (pairing.flip (basis i)) (∑ k, dualBasis.repr x k • dualBasis k) = _
      rw [map_sum]
      simp only [map_smul, LinearMap.BilinForm.flip_apply, dual, smul_eq_mul]
      simp
    rw [← dualBasis.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    have integral_coordinate : dualBasis.repr x i ∈ (1 : Submodule R K) := by
      rw [← coordinates]
      exact (LinearMap.BilinForm.mem_dualSubmodule pairing).mp hx
        (basis i) (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨coefficient, coefficient_eq⟩ := Submodule.mem_one.mp integral_coordinate
    rw [← coefficient_eq]
    simpa only [IsScalarTower.algebraMap_smul] using
      (Submodule.span R (Set.range dualBasis)).smul_mem coefficient
        (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change dualBasis i ∈ pairing.dualSubmodule (Submodule.span R (Set.range basis))
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    let integral_pairings : Submodule R M :=
      Submodule.comap ((pairing (dualBasis i)).restrictScalars R) (1 : Submodule R K)
    have generators : Set.range basis ⊆ integral_pairings := by
      rintro _ ⟨j, rfl⟩
      change pairing (dualBasis i) (basis j) ∈ (1 : Submodule R K)
      rw [dual]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact Submodule.mem_one.mpr ⟨0, map_zero _⟩
    exact Submodule.span_le.mpr generators

end DualBases

section ExtendedTraceDual

variable (K F L S : Type*) [Field K] [Field F] [Field L] [CommRing S]
  [Algebra K F] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra S F]
  {ι : Type*} [Finite ι] [DecidableEq ι]

/-- In the actual scalar-extended algebra, the trace dual of the extended basis
lattice is generated by the extended original trace-dual basis. -/
theorem traceDual_span_baseChange (basis : Module.Basis ι K L) :
    (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule (R := S)
        (Submodule.span S (Set.range (basis.baseChange F))) =
      Submodule.span S (Set.range (basis.traceDual.baseChange F)) := by
  apply dualSubmodule_span_of_dualBases
  intro i j
  simp only [Module.Basis.baseChange_apply, Algebra.traceForm_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [trace_one_tmul, basis.trace_traceDual_mul]
  simp [eq_comm]

end ExtendedTraceDual

section LatticeExtension

variable (R S K F L : Type*) [CommRing R] [CommRing S] [Field K] [Field F] [Field L]
  [Algebra R K] [Algebra R S] [Algebra R F] [Algebra S F] [Algebra K F]
  [Algebra R L] [Algebra K L]
  [IsScalarTower R K F] [IsScalarTower R S F] [IsScalarTower R K L]

/-- Extend an actual lattice by taking its image in the tensor algebra and
spanning over the new integral scalar ring. -/
noncomputable def extendLattice (lattice : Submodule R L) : Submodule S (F ⊗[K] L) :=
  Submodule.span S ((fun x : L => (1 : F) ⊗ₜ[K] x) '' (lattice : Set L))

/-- Extending a generated lattice extends its generators. -/
theorem extendLattice_span {ι : Type*} (generators : ι → L) :
    extendLattice R S K F L (Submodule.span R (Set.range generators)) =
      Submodule.span S (Set.range (fun i => (1 : F) ⊗ₜ[K] generators i)) := by
  let inclusion : L →ₗ[R] F ⊗[K] L := (TensorProduct.mk K F L 1).restrictScalars R
  let extended := Submodule.span S (Set.range (fun i => (1 : F) ⊗ₜ[K] generators i))
  have maps_into : Submodule.span R (Set.range generators) ≤
      Submodule.comap inclusion (extended.restrictScalars R) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · rw [extendLattice, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact maps_into hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨generators i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩

/-- The same generator transport for an arbitrary set of elements. -/
theorem extendLattice_span_set (generators : Set L) :
    extendLattice R S K F L (Submodule.span R generators) =
      Submodule.span S ((fun x : L => (1 : F) ⊗ₜ[K] x) '' generators) := by
  have original_range : Set.range (fun x : generators => (x : L)) = generators := by
    ext x
    simp
  have extended_range : Set.range (fun x : generators => (1 : F) ⊗ₜ[K] (x : L)) =
      (fun x : L => (1 : F) ⊗ₜ[K] x) '' generators := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  simpa only [original_range, extended_range] using
    extendLattice_span R S K F L (fun x : generators => (x : L))

/-- Scalar extension preserves the actual product of two lattices. -/
theorem extendLattice_mul (left right : Submodule R L) :
    extendLattice R S K F L (left * right) =
      extendLattice R S K F L left * extendLattice R S K F L right := by
  rw [Submodule.mul_def, extendLattice_span_set]
  change Submodule.span S _ = Submodule.span S _ * Submodule.span S _
  rw [Submodule.span_mul_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨1 ⊗ₜ[K] a, ⟨a, ha, rfl⟩, 1 ⊗ₜ[K] b, ⟨b, hb, rfl⟩,
      by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a * b, ⟨a, ha, b, hb, rfl⟩, by simp [Algebra.TensorProduct.tmul_mul_tmul]⟩

omit [Algebra R K] [Algebra R S] [Algebra R F]
  [IsScalarTower R K F] [IsScalarTower R S F] [IsScalarTower R K L] in
theorem extendLattice_mono {left right : Submodule R L} (inclusion : left ≤ right) :
    extendLattice R S K F L left ≤ extendLattice R S K F L right :=
  Submodule.span_mono (Set.image_mono inclusion)

omit [Algebra R K] [Algebra R S] [Algebra R F]
  [IsScalarTower R K F] [IsScalarTower R S F] [IsScalarTower R K L] in
/-- Extending an integral order retains its unit. -/
theorem one_le_extendLattice {order : Submodule R L} (contains_one : 1 ≤ order) :
    1 ≤ extendLattice R S K F L order := by
  rw [Submodule.one_le]
  exact Submodule.subset_span ⟨1, Submodule.one_le.mp contains_one, rfl⟩

/-- An actual inverse-lattice identity remains a quotient identity after
extension. Its hypotheses will be supplied by the classical different. -/
theorem extendLattice_eq_quotient_of_inverse
    (order different codifferent : Submodule R L)
    (contains_one : 1 ≤ order) (stable : order * different ≤ different)
    (inverse : different * codifferent = order) :
    extendLattice R S K F L different =
      extendLattice R S K F L order / extendLattice R S K F L codifferent := by
  apply lattice_eq_quotient_of_inverse
  · exact one_le_extendLattice R S K F L contains_one
  · rw [← extendLattice_mul]
    exact extendLattice_mono R S K F L stable
  · rw [← extendLattice_mul, inverse]

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
  {ι : Type*} [Finite ι]

/-- Trace duality commutes with extension of a lattice generated by a field
basis, with both sides referring to the actual lattice image. -/
theorem traceDual_extend_basis_lattice (basis : Module.Basis ι K L) :
    (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule
        (extendLattice R S K F L (Submodule.span R (Set.range basis))) =
      extendLattice R S K F L
        ((Algebra.traceForm K L).dualSubmodule (Submodule.span R (Set.range basis))) := by
  classical
  have original_dual := dualSubmodule_span_of_dualBases R K L
    (Algebra.traceForm K L) basis basis.traceDual (by
      intro i j
      simpa only [Algebra.traceForm_apply, eq_comm] using basis.trace_traceDual_mul i j)
  rw [original_dual, extendLattice_span, extendLattice_span]
  have extended_basis : (fun i => (1 : F) ⊗ₜ[K] basis i) = ⇑(basis.baseChange F) := by
    funext i
    exact (Module.Basis.baseChange_apply F basis i).symm
  have extended_dual_basis : (fun i => (1 : F) ⊗ₜ[K] basis.traceDual i) =
      ⇑(basis.traceDual.baseChange F) := by
    funext i
    exact (Module.Basis.baseChange_apply F basis.traceDual i).symm
  rw [extended_basis, extended_dual_basis]
  exact traceDual_span_baseChange K F L S basis

end LatticeExtension

section ClassicalDifferentInverse

variable (R K B L : Type*) [CommRing R] [Field K] [CommRing B] [Field L]
  [Algebra R K] [Algebra R B] [Algebra B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]
  [IsDomain R] [IsFractionRing R K] [IsIntegrallyClosed R]
  [IsDedekindDomain B] [Module.IsTorsionFree R B] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B R L]

/-- The actual classical different and trace-dual lattices multiply to the
integral image. This is derived from the nonzero fractional codifferent. -/
theorem different_mul_traceDual :
    IsLocalization.coeSubmodule L (differentIdeal R B) *
      Submodule.traceDual R K (1 : Submodule B L) = 1 := by
  let codifferent : FractionalIdeal (nonZeroDivisors B) L := FractionalIdeal.dual R K 1
  have nonzero : codifferent ≠ 0 := FractionalIdeal.dual_ne_zero_iff.mpr one_ne_zero
  have inverse : codifferent⁻¹ * codifferent = 1 := inv_mul_cancel₀ nonzero
  have underlying := congrArg
    (fun ideal : FractionalIdeal (nonZeroDivisors B) L => (ideal : Submodule B L)) inverse
  have codifferent_eq : (codifferent : Submodule B L) = Submodule.traceDual R K 1 :=
    FractionalIdeal.coe_dual_one R K L B
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_inv_of_ne_zero L nonzero,
    codifferent_eq, FractionalIdeal.coe_one] at underlying
  rw [coeSubmodule_differentIdeal R K B]
  simpa only [IsLocalization.coeSubmodule_top] using underlying

variable (S F : Type*) [CommRing S] [Field F]
  [Algebra R S] [Algebra R F] [Algebra S F] [Algebra K F]
  [IsScalarTower R K F] [IsScalarTower R S F]

/-- Extension of the actual classical different is the quotient of the
extended integral image by the extended actual codifferent. -/
theorem extended_different_eq_quotient :
    extendLattice R S K F L
        ((IsLocalization.coeSubmodule L (differentIdeal R B)).restrictScalars R) =
      extendLattice R S K F L ((1 : Submodule B L).restrictScalars R) /
        extendLattice R S K F L
          ((Submodule.traceDual R K (1 : Submodule B L)).restrictScalars R) := by
  apply extendLattice_eq_quotient_of_inverse
  · rw [Submodule.one_le]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  · rw [← Submodule.restrictScalars_mul, one_mul]
  · rw [← Submodule.restrictScalars_mul, different_mul_traceDual R K B L]

variable [Module.Free R B] [Module.Finite R B]

omit [IsIntegrallyClosed R] [Module.IsTorsionFree R B] [IsIntegralClosure B R L] in
/-- Trace duality commutes with extension of the actual integral image of a
finite free integral closure. The required field basis is constructed from
an integral basis by localization. -/
theorem traceDual_extend_integralImage :
    (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule
        (extendLattice R S K F L ((1 : Submodule B L).restrictScalars R)) =
      extendLattice R S K F L
        ((Submodule.traceDual R K (1 : Submodule B L)).restrictScalars R) := by
  let integralBasis := Module.Free.chooseBasis R B
  let fieldBasis := integralBasis.localizationLocalization K (nonZeroDivisors R) L
  have span_eq : Submodule.span R (Set.range fieldBasis) =
      (1 : Submodule B L).restrictScalars R := by
    rw [integralBasis.localizationLocalization_span K (nonZeroDivisors R) L]
    ext x
    exact Submodule.mem_one.symm
  have dual_eq : (Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars R) =
      (Submodule.traceDual R K (1 : Submodule B L)).restrictScalars R := by
    ext x
    change x ∈ (Algebra.traceForm K L).dualSubmodule
      ((1 : Submodule B L).restrictScalars R) ↔ x ∈ Submodule.traceDual R K 1
    rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_traceDual]
    exact forall_congr' fun y => forall_congr' fun _ => Submodule.mem_one
  simpa only [span_eq, dual_eq] using traceDual_extend_basis_lattice R S K F L fieldBasis

/-- The extended classical different is exactly the quotient by the trace
dual computed in the actual tensor algebra. No inverse-lattice identity or
trace comparison is assumed. -/
theorem extended_different_eq_traceQuotient :
    extendLattice R S K F L
        ((IsLocalization.coeSubmodule L (differentIdeal R B)).restrictScalars R) =
      extendLattice R S K F L ((1 : Submodule B L).restrictScalars R) /
        (Algebra.traceForm F (F ⊗[K] L)).dualSubmodule
          (extendLattice R S K F L ((1 : Submodule B L).restrictScalars R)) := by
  rw [traceDual_extend_integralImage R K B L S F]
  exact extended_different_eq_quotient R K B L S F

end ClassicalDifferentInverse

section NumberFieldDifferent

open NumberField

variable (L S F : Type*) [Field L] [NumberField L] [CommRing S] [Field F]
  [Algebra ℚ F] [Algebra S F]

/-- For a number field, the actual ring of integers supplies all finite free
integral-closure hypotheses. In particular this applies to extension from
the integers to the p-adic integers inside the p-adic field. -/
theorem numberField_extended_different_eq_traceQuotient :
    extendLattice ℤ S ℚ F L
        ((IsLocalization.coeSubmodule L (differentIdeal ℤ (𝓞 L))).restrictScalars ℤ) =
      extendLattice ℤ S ℚ F L ((1 : Submodule (𝓞 L) L).restrictScalars ℤ) /
        (Algebra.traceForm F (F ⊗[ℚ] L)).dualSubmodule
          (extendLattice ℤ S ℚ F L ((1 : Submodule (𝓞 L) L).restrictScalars ℤ)) :=
  extended_different_eq_traceQuotient ℤ ℚ (𝓞 L) L S F

end NumberFieldDifferent

end LeanFormal.IUT.DifferentTraceBaseChange
