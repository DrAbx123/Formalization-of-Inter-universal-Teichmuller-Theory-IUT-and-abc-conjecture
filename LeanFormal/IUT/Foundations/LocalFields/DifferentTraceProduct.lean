import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.Tactic

/-!
# Trace duals for finite products

Classical `differentIdeal` requires a domain. A product of completed fields is
instead treated through its actual trace-pairing dual lattice and the ideal of
elements multiplying that lattice into the integral algebra. This is the
independent product-algebra step in global/local different compatibility.
-/

namespace LeanFormal.IUT.DifferentTraceProduct

open scoped BigOperators

section ProductTrace

variable (K : Type*) [Field K] {ι : Type*} [Fintype ι]
  (A : ι → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
  [∀ i, FiniteDimensional K (A i)]

/-- The trace of a finite product algebra is the sum of its component traces. -/
theorem trace_pi (x : ∀ i, A i) :
    Algebra.trace K (∀ i, A i) x = ∑ i, Algebra.trace K (A i) (x i) := by
  classical
  let bases := fun i => Module.Free.chooseBasis K (A i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis bases)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.trace_eq_matrix_trace (bases i)]
  simp [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Pi.basis_repr, Pi.basis_apply]

end ProductTrace

section TraceDual

variable (R K B A : Type*) [CommRing R] [Field K] [CommRing B] [CommRing A]
  [Algebra R K] [Algebra R B] [Algebra B A] [Algebra K A] [Algebra R A]
  [IsScalarTower R K A] [IsScalarTower R B A]

/-- The trace dual of the actual image of the integral algebra, also defined
when the ambient algebra is a product rather than a field. -/
noncomputable def traceDualLattice : Submodule R A :=
  (Algebra.traceForm K A).dualSubmodule ((1 : Submodule B A).restrictScalars R)

/-- The ideal carrying the trace-dual lattice into the actual integral algebra. -/
noncomputable def traceMultiplierIdeal : Ideal B where
  carrier := {b | ∀ x ∈ traceDualLattice R K B A,
    algebraMap B A b * x ∈ (1 : Submodule B A)}
  zero_mem' := by
    intro x _
    simpa only [map_zero, zero_mul] using (1 : Submodule B A).zero_mem
  add_mem' := by
    intro b c hb hc x hx
    simpa only [map_add, add_mul] using (1 : Submodule B A).add_mem (hb x hx) (hc x hx)
  smul_mem' := by
    intro b c hc x hx
    simpa only [smul_eq_mul, map_mul, mul_assoc, Algebra.smul_def] using
      (1 : Submodule B A).smul_mem b (hc x hx)

theorem mem_traceMultiplierIdeal (b : B) :
    b ∈ traceMultiplierIdeal R K B A ↔ ∀ x ∈ traceDualLattice R K B A,
      algebraMap B A b * x ∈ (1 : Submodule B A) := Iff.rfl

end TraceDual

section ProductDual

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
  {ι : Type*} [Finite ι] (A : ι → Type*)
  [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Algebra K (A i)]
  [∀ i, IsScalarTower R K (A i)] [∀ i, FiniteDimensional K (A i)]

/-- The trace dual of a product lattice is its componentwise trace dual. -/
theorem dualSubmodule_pi (lattices : ∀ i, Submodule R (A i)) :
    (Algebra.traceForm K (∀ i, A i)).dualSubmodule (Submodule.pi Set.univ lattices) =
    Submodule.pi Set.univ (fun i => (Algebra.traceForm K (A i)).dualSubmodule (lattices i)) := by
  classical
  letI := Fintype.ofFinite ι
  ext x
  simp only [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · intro hx i y hy
    have single_mem : ∀ k, Pi.single i y k ∈ lattices k := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa using hy
      · simp [Pi.single_eq_of_ne hki]
    have single_trace := hx (Pi.single i y) single_mem
    rw [Algebra.traceForm_apply, trace_pi] at single_trace
    have diagonal_sum :
        (∑ k, Algebra.trace K (A k) (x k * Pi.single i y k)) =
          Algebra.trace K (A i) (x i * y) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki
        simp [Pi.single_eq_of_ne hki]
      · simp
    change (∑ k, Algebra.trace K (A k) (x k * Pi.single i y k)) ∈
      (1 : Submodule R K) at single_trace
    rwa [diagonal_sum] at single_trace
  · intro hx y hy
    rw [Algebra.traceForm_apply, trace_pi]
    exact Submodule.sum_mem (1 : Submodule R K) fun i _ => hx i (y i) (hy i)

end ProductDual

section IntegralProduct

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
  {ι : Type*} [Finite ι] (B A : ι → Type*)
  [∀ i, CommRing (B i)] [∀ i, CommRing (A i)]
  [∀ i, Algebra R (B i)] [∀ i, Algebra (B i) (A i)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra K (A i)]
  [∀ i, IsScalarTower R K (A i)] [∀ i, IsScalarTower R (B i) (A i)]
  [∀ i, FiniteDimensional K (A i)]

omit [Finite ι] in
/-- Membership in the image of a product algebra is componentwise. -/
theorem mem_integralImage_pi (x : ∀ i, A i) :
    x ∈ (1 : Submodule (∀ i, B i) (∀ i, A i)) ↔
      ∀ i, x i ∈ (1 : Submodule (B i) (A i)) := by
  classical
  simp only [Submodule.mem_one]
  constructor
  · rintro ⟨b, hb⟩ i
    exact ⟨b i, congrFun hb i⟩
  · intro hx
    choose b hb using hx
    exact ⟨b, funext hb⟩

omit [Finite ι] in
/-- The integral image lattice of a product is the product of the images. -/
theorem integralImage_pi :
    (1 : Submodule (∀ i, B i) (∀ i, A i)).restrictScalars R =
      Submodule.pi Set.univ (fun i => (1 : Submodule (B i) (A i)).restrictScalars R) := by
  ext x
  change x ∈ (1 : Submodule (∀ i, B i) (∀ i, A i)) ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left]
  exact mem_integralImage_pi B A x

/-- Trace-dual lattices of actual integral algebras commute with finite products. -/
theorem traceDualLattice_pi :
    traceDualLattice R K (∀ i, B i) (∀ i, A i) =
      Submodule.pi Set.univ (fun i => traceDualLattice R K (B i) (A i)) := by
  unfold traceDualLattice
  rw [integralImage_pi, dualSubmodule_pi]

/-- The trace multiplier ideal of a finite product is componentwise. -/
theorem mem_traceMultiplierIdeal_pi (b : ∀ i, B i) :
    b ∈ traceMultiplierIdeal R K (∀ i, B i) (∀ i, A i) ↔
      ∀ i, b i ∈ traceMultiplierIdeal R K (B i) (A i) := by
  classical
  simp only [mem_traceMultiplierIdeal, traceDualLattice_pi, Submodule.mem_pi,
    Set.mem_univ, forall_true_left, mem_integralImage_pi]
  constructor
  · intro hb i x hx
    have single_mem : ∀ k, Pi.single i x k ∈ traceDualLattice R K (B k) (A k) := by
      intro k
      by_cases hki : k = i
      · subst k
        simpa using hx
      · simp [Pi.single_eq_of_ne hki]
    have map_apply : algebraMap (∀ k, B k) (∀ k, A k) b i =
        algebraMap (B i) (A i) (b i) := rfl
    simpa only [Pi.mul_apply, Pi.single_eq_same, map_apply] using
      hb (Pi.single i x) single_mem i
  · intro hb x hx i
    exact hb i (x i) (hx i)

end IntegralProduct

section ClassicalDifferent

variable (R K B L : Type*) [CommRing R] [Field K] [CommRing B] [Field L]
  [Algebra R K] [Algebra R B] [Algebra B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]
  [IsDomain R] [IsFractionRing R K] [IsIntegrallyClosed R]
  [IsDedekindDomain B] [Module.IsTorsionFree R B] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B R L]

/-- On an actual Dedekind integral closure in its fraction field, the multiplier
construction is exactly Mathlib's classical different ideal. -/
theorem traceMultiplierIdeal_eq_differentIdeal :
    traceMultiplierIdeal R K B L = differentIdeal R B := by
  ext b
  have different_eq := coeSubmodule_differentIdeal R K B (L := L)
  rw [mem_traceMultiplierIdeal]
  constructor
  · intro hb
    have image_mem : algebraMap B L b ∈ IsLocalization.coeSubmodule L (differentIdeal R B) := by
      rw [different_eq, Submodule.mem_div_iff_forall_mul_mem]
      intro x hx
      exact hb x hx
    obtain ⟨c, hc, hcb⟩ := image_mem
    have cb : c = b := IsFractionRing.injective B L hcb
    subst c
    exact hc
  · intro hb x hx
    have image_mem : algebraMap B L b ∈ IsLocalization.coeSubmodule L (differentIdeal R B) :=
      ⟨b, hb, rfl⟩
    rw [different_eq, Submodule.mem_div_iff_forall_mul_mem] at image_mem
    exact image_mem x hx

end ClassicalDifferent

section ProductDifferent

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsFractionRing R K] [IsIntegrallyClosed R]
  {ι : Type*} [Finite ι] (B L : ι → Type*)
  [∀ i, CommRing (B i)] [∀ i, Field (L i)]
  [∀ i, Algebra R (B i)] [∀ i, Algebra (B i) (L i)]
  [∀ i, Algebra R (L i)] [∀ i, Algebra K (L i)]
  [∀ i, IsScalarTower R K (L i)] [∀ i, IsScalarTower R (B i) (L i)]
  [∀ i, IsDedekindDomain (B i)] [∀ i, Module.IsTorsionFree R (B i)]
  [∀ i, IsFractionRing (B i) (L i)] [∀ i, FiniteDimensional K (L i)]
  [∀ i, Algebra.IsSeparable K (L i)] [∀ i, IsIntegralClosure (B i) R (L i)]

/-- The trace multiplier ideal of a product of genuine integral closures is
exactly the product of their classical different ideals, expressed elementwise. -/
theorem mem_traceMultiplierIdeal_pi_iff_mem_differentIdeal (b : ∀ i, B i) :
    b ∈ traceMultiplierIdeal R K (∀ i, B i) (∀ i, L i) ↔
      ∀ i, b i ∈ differentIdeal R (B i) := by
  rw [mem_traceMultiplierIdeal_pi]
  simp only [traceMultiplierIdeal_eq_differentIdeal R K]

end ProductDifferent

end LeanFormal.IUT.DifferentTraceProduct
