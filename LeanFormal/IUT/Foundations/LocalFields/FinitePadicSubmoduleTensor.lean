import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorIntegralRegion

/-!
# Integral submodule tensors inside the actual finite Qp tensor

This constructs the natural map and its actual image. For free integral
submodules with full Qp span, fraction-field extension of their bases
proves injectivity. Compact factor submodules provide finite, free,
compact images; finite integral bases also prove openness.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]
variable (S : (i : ι) → Submodule ℤ_[p] (M i))

def submoduleTensorSpan : Submodule ℤ_[p] (FinitePadicTensor (p := p) M) :=
  Submodule.span ℤ_[p] (tensorIntegralRegion (p := p) M (fun i => (S i : Set (M i))))

def submoduleTensorMap : (PiTensorProduct ℤ_[p] (fun i => S i)) →ₗ[ℤ_[p]]
    FinitePadicTensor (p := p) M :=
  PiTensorProduct.lift (((finitePadicTensorTprod (p := p) M).restrictScalars ℤ_[p]).compLinearMap
    (fun i => (S i).subtype))

theorem submoduleTensorMap_tprod (x : (i : ι) → S i) :
    submoduleTensorMap (p := p) M S (PiTensorProduct.tprod ℤ_[p] x) =
      finitePadicTensorTprod (p := p) M (fun i => (x i : M i)) :=
  PiTensorProduct.lift.tprod x

theorem range_submoduleTensorMap :
    LinearMap.range (submoduleTensorMap (p := p) M S) = submoduleTensorSpan (p := p) M S := by
  apply le_antisymm
  · rw [← Submodule.map_top, ← PiTensorProduct.span_tprod_eq_top, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    rw [submoduleTensorMap_tprod]
    exact Submodule.subset_span ⟨fun i => (x i : M i), fun i _ => (x i).property, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨PiTensorProduct.tprod ℤ_[p] (fun i => ⟨x i, hx i (Set.mem_univ i)⟩), ?_⟩
    exact submoduleTensorMap_tprod (p := p) M S _

theorem finite_submoduleTensorSpan (hS : ∀ i, IsCompact (S i : Set (M i))) :
    Module.Finite ℤ_[p] (submoduleTensorSpan (p := p) M S) :=
  finite_span_of_isCompact (p := p) _ (isCompact_tensorIntegralRegion M _ hS)

theorem free_submoduleTensorSpan (hS : ∀ i, IsCompact (S i : Set (M i))) :
    Module.Free ℤ_[p] (submoduleTensorSpan (p := p) M S) :=
  free_span_of_isCompact (p := p) _ (isCompact_tensorIntegralRegion M _ hS)

theorem isCompact_submoduleTensorSpan (hS : ∀ i, IsCompact (S i : Set (M i))) :
    IsCompact (submoduleTensorSpan (p := p) M S : Set (FinitePadicTensor (p := p) M)) :=
  isCompact_span_of_isCompact (p := p) _ (isCompact_tensorIntegralRegion M _ hS)

theorem submoduleTensorSpan_mono (T : (i : ι) → Submodule ℤ_[p] (M i))
    (hST : ∀ i, S i ≤ T i) : submoduleTensorSpan (p := p) M S ≤
      submoduleTensorSpan (p := p) M T := by
  apply Submodule.span_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, fun i hi => hST i (hx i hi), rfl⟩

variable [∀ i, Module.Free ℤ_[p] (S i)]

def submoduleTensorPadicBasis
    (hspan : ∀ i, Submodule.span ℚ_[p] (S i : Set (M i)) = ⊤) :
    Module.Basis ((i : ι) → Module.Free.ChooseBasisIndex ℤ_[p] (S i)) ℚ_[p]
      (FinitePadicTensor (p := p) M) :=
  Basis.piTensorProduct (fun i => padicBasisOfIntegralBasis (S i)
    (Module.Free.chooseBasis ℤ_[p] (S i)) (hspan i))

omit [∀ i, FiniteDimensional ℚ_[p] (M i)] in
theorem submoduleTensorPadicBasis_mem_region
    (hspan : ∀ i, Submodule.span ℚ_[p] (S i : Set (M i)) = ⊤)
    (j : (i : ι) → Module.Free.ChooseBasisIndex ℤ_[p] (S i)) :
    submoduleTensorPadicBasis (p := p) M S hspan j ∈
      tensorIntegralRegion (p := p) M (fun i => (S i : Set (M i))) := by
  refine ⟨fun i => (Module.Free.chooseBasis ℤ_[p] (S i) (j i) : M i),
    fun i _ => Subtype.property _, ?_⟩
  change PiTensorProduct.tprod ℚ_[p] _ = (Basis.piTensorProduct _ ) j
  rw [Basis.piTensorProduct_apply]
  congr 1
  funext i
  exact (padicBasisOfIntegralBasis_apply _ _ _ _).symm

theorem submoduleTensorMap_injective
    (hspan : ∀ i, Submodule.span ℚ_[p] (S i : Set (M i)) = ⊤) :
    Function.Injective (submoduleTensorMap (p := p) M S) := by
  letI : IsScalarTower ℤ_[p] ℚ_[p] (FinitePadicTensor (p := p) M) := {
    smul_assoc := fun z q x => by
      change ((z : ℚ_[p]) * q) • x = (z : ℚ_[p]) • (q • x)
      exact mul_smul (z : ℚ_[p]) q x }
  have hvalues : submoduleTensorMap (p := p) M S ∘
      Basis.piTensorProduct (fun i => Module.Free.chooseBasis ℤ_[p] (S i)) =
        submoduleTensorPadicBasis (p := p) M S hspan := by
    funext j
    simp only [Function.comp_apply, Basis.piTensorProduct_apply, submoduleTensorMap_tprod]
    change PiTensorProduct.tprod ℚ_[p] _ = (Basis.piTensorProduct _ ) j
    rw [Basis.piTensorProduct_apply]
    congr 1
    funext i
    exact (padicBasisOfIntegralBasis_apply _ _ _ _).symm
  apply LinearMap.injective_of_linearIndependent
    (Basis.piTensorProduct (fun i => Module.Free.chooseBasis ℤ_[p] (S i))).span_eq
  rw [hvalues]
  exact (LinearIndependent.iff_fractionRing ℤ_[p] ℚ_[p]
    (V := FinitePadicTensor (p := p) M)).mpr (submoduleTensorPadicBasis M S hspan).linearIndependent

def submoduleTensorEquivSpan
    (hspan : ∀ i, Submodule.span ℚ_[p] (S i : Set (M i)) = ⊤) :
    (PiTensorProduct ℤ_[p] (fun i => S i)) ≃ₗ[ℤ_[p]] submoduleTensorSpan (p := p) M S :=
  (LinearEquiv.ofInjective (submoduleTensorMap (p := p) M S)
    (submoduleTensorMap_injective (p := p) M S hspan)).trans
      (LinearEquiv.ofEq _ _ (range_submoduleTensorMap (p := p) M S))

theorem padic_span_submoduleTensorSpan_eq_top
    (hspan : ∀ i, Submodule.span ℚ_[p] (S i : Set (M i)) = ⊤) :
    Submodule.span ℚ_[p] (submoduleTensorSpan (p := p) M S :
      Set (FinitePadicTensor (p := p) M)) = ⊤ := by
  apply top_unique
  rw [← (submoduleTensorPadicBasis M S hspan).span_eq]
  apply Submodule.span_mono
  rintro x ⟨j, rfl⟩
  exact Submodule.subset_span (submoduleTensorPadicBasis_mem_region M S hspan j)

theorem isOpen_submoduleTensorSpan [∀ i, Module.Finite ℤ_[p] (S i)]
    (hspan : ∀ i, Submodule.span ℚ_[p] (S i : Set (M i)) = ⊤) :
    IsOpen (submoduleTensorSpan (p := p) M S : Set (FinitePadicTensor (p := p) M)) := by
  apply isOpen_of_basis_mem (submoduleTensorPadicBasis M S hspan)
  intro j
  exact Submodule.subset_span (submoduleTensorPadicBasis_mem_region M S hspan j)

end

end LeanFormal.IUT.LocalFieldPadicTensor
