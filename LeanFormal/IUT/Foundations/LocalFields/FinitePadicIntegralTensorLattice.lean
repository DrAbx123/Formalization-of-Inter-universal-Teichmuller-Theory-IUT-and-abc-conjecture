import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRegion

/-!
# The integral span of actual logarithmic pure tensors

The integral lattice here is the Zp span inside the genuine Qp tensor.
Compactness of the actual pure-tensor region proves finite generation.
Tensoring actual Qp bases contained in the local shells proves openness
and full Qp span, including the empty factor family.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldLogarithm LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (A : ι → Type*) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]

def tensorLogShellLattice : Submodule ℤ_[p] (FinitePadicTensor (p := p) A) :=
  Submodule.span ℤ_[p] (tensorLogShellRegion (p := p) A)

theorem tensorLogShellRegion_subset_lattice :
    tensorLogShellRegion (p := p) A ⊆ tensorLogShellLattice (p := p) A :=
  Submodule.subset_span

instance tensorLogShellLatticeFinite :
    Module.Finite ℤ_[p] (tensorLogShellLattice (p := p) A) :=
  finite_span_of_isCompact (p := p) _ (isCompact_tensorLogShellRegion A)

instance tensorLogShellLatticeFree :
    Module.Free ℤ_[p] (tensorLogShellLattice (p := p) A) :=
  free_span_of_isCompact (p := p) _ (isCompact_tensorLogShellRegion A)

theorem isCompact_tensorLogShellLattice :
    IsCompact (tensorLogShellLattice (p := p) A : Set (FinitePadicTensor (p := p) A)) :=
  isCompact_span_of_isCompact (p := p) _ (isCompact_tensorLogShellRegion A)

omit [Fintype ι] in
theorem exists_basis_mem_tensorLogShellRegion [Finite ι] :
    ∃ basis : Module.Basis (FinitePadicTensorIndex (p := p) A) ℚ_[p]
      (FinitePadicTensor (p := p) A), ∀ j, basis j ∈ tensorLogShellRegion (p := p) A := by
  classical
  letI := Fintype.ofFinite ι
  choose basis hmem using
    (fun i => exists_basis_mem_integralLogShellLattice (K := A i) (p := p))
  refine ⟨Basis.piTensorProduct basis, ?_⟩
  intro j
  refine ⟨fun i => basis i (j i), ?_, ?_⟩
  · intro i _
    exact hmem i (j i)
  · exact (Basis.piTensorProduct_apply basis j).symm

theorem isOpen_tensorLogShellLattice :
    IsOpen (tensorLogShellLattice (p := p) A : Set (FinitePadicTensor (p := p) A)) := by
  obtain ⟨basis, hmem⟩ := exists_basis_mem_tensorLogShellRegion (p := p) A
  exact isOpen_of_basis_mem basis _
    (fun j => tensorLogShellRegion_subset_lattice (p := p) A (hmem j))

omit [Fintype ι] in
theorem padic_span_tensorLogShellRegion_eq_top [Finite ι] :
    Submodule.span ℚ_[p] (tensorLogShellRegion (p := p) A) = ⊤ := by
  obtain ⟨basis, hmem⟩ := exists_basis_mem_tensorLogShellRegion (p := p) A
  apply top_unique
  rw [← basis.span_eq]
  apply Submodule.span_mono
  rintro x ⟨j, rfl⟩
  exact hmem j

theorem padic_span_tensorLogShellLattice_eq_top :
    Submodule.span ℚ_[p] (tensorLogShellLattice (p := p) A :
      Set (FinitePadicTensor (p := p) A)) = ⊤ := by
  apply top_unique
  rw [← padic_span_tensorLogShellRegion_eq_top (p := p) A]
  exact Submodule.span_mono (tensorLogShellRegion_subset_lattice (p := p) A)

def integralLogTensorToPadicTensor :
    (PiTensorProduct ℤ_[p] (fun i => integralLogShellLattice (K := A i) (p := p))) →ₗ[ℤ_[p]]
      FinitePadicTensor (p := p) A :=
  PiTensorProduct.lift
    (((finitePadicTensorTprod (p := p) A).restrictScalars ℤ_[p]).compLinearMap
      (fun i => (integralLogShellLattice (K := A i) (p := p)).subtype))

theorem integralLogTensorToPadicTensor_tprod
    (x : (i : ι) → integralLogShellLattice (K := A i) (p := p)) :
    integralLogTensorToPadicTensor (p := p) A (PiTensorProduct.tprod ℤ_[p] x) =
      finitePadicTensorTprod (p := p) A (fun i => (x i : A i)) :=
  PiTensorProduct.lift.tprod x

theorem range_integralLogTensorToPadicTensor :
    LinearMap.range (integralLogTensorToPadicTensor (p := p) A) =
      tensorLogShellLattice (p := p) A := by
  apply le_antisymm
  · rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [integralLogTensorToPadicTensor_tprod]
    apply tensorLogShellRegion_subset_lattice (p := p) A
    exact ⟨fun i => (x i : A i), fun i _ => (x i).property, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨PiTensorProduct.tprod ℤ_[p] (fun i => ⟨x i, hx i (Set.mem_univ i)⟩), ?_⟩
    exact integralLogTensorToPadicTensor_tprod (p := p) A _

theorem integralLogTensorToPadicTensor_injective :
    Function.Injective (integralLogTensorToPadicTensor (p := p) A) := by
  classical
  letI : IsScalarTower ℤ_[p] ℚ_[p] (FinitePadicTensor (p := p) A) := {
    smul_assoc := fun z q x => by
      change ((z : ℚ_[p]) * q) • x = (z : ℚ_[p]) • (q • x)
      exact mul_smul (z : ℚ_[p]) q x }
  let integralBasis := fun i => Module.Free.chooseBasis ℤ_[p]
    (integralLogShellLattice (K := A i) (p := p))
  let rationalBasis := fun i => padicBasisOfIntegralBasis
    (integralLogShellLattice (K := A i) (p := p)) (integralBasis i)
    (span_padic_integralLogShellLattice_eq_top (K := A i) (p := p))
  have hvalues : integralLogTensorToPadicTensor (p := p) A ∘
      Basis.piTensorProduct integralBasis = Basis.piTensorProduct rationalBasis := by
    funext j
    simp only [Function.comp_apply, Basis.piTensorProduct_apply,
      integralLogTensorToPadicTensor_tprod]
    change PiTensorProduct.tprod ℚ_[p] (fun i => (integralBasis i (j i) : A i)) =
      PiTensorProduct.tprod ℚ_[p] (fun i => rationalBasis i (j i))
    congr 1
    funext i
    exact (padicBasisOfIntegralBasis_apply _ _ _ _).symm
  apply LinearMap.injective_of_linearIndependent (Basis.piTensorProduct integralBasis).span_eq
  rw [hvalues]
  exact (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]
    (V := FinitePadicTensor (p := p) A)).mpr
    (Basis.piTensorProduct rationalBasis).linearIndependent

def integralLogTensorEquivLattice :
    (PiTensorProduct ℤ_[p] (fun i => integralLogShellLattice (K := A i) (p := p))) ≃ₗ[ℤ_[p]]
      tensorLogShellLattice (p := p) A :=
  (LinearEquiv.ofInjective (integralLogTensorToPadicTensor (p := p) A)
    (integralLogTensorToPadicTensor_injective (p := p) A)).trans
    (LinearEquiv.ofEq _ _ (range_integralLogTensorToPadicTensor (p := p) A))

theorem finrank_tensorLogShellLattice :
    Module.finrank ℤ_[p] (tensorLogShellLattice (p := p) A) =
      Module.finrank ℚ_[p] (FinitePadicTensor (p := p) A) :=
  finrank_of_full_integral_submodule _ (padic_span_tensorLogShellLattice_eq_top (p := p) A)

end

end LeanFormal.IUT.LocalFieldPadicTensor
