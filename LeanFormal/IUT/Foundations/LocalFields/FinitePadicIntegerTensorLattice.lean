import LeanFormal.IUT.Foundations.LocalFields.FinitePadicSubmoduleTensor
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicIntegralTensorLattice
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductUnitRegionMaps

/-!
# The true tensor of local valuation integers

The Zp span of pure integer tensors is the image of the actual Zp tensor
of the local valuation integer lattices. Its map is injective, its image
is compact open and full rank, and it is contained in the actual integral
log-shell tensor lattice. Powers preserve the compact pure integer region.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldLogarithm LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicIntegralLattice
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

noncomputable section

variable {p : ℕ} [Fact p.Prime]

theorem span_padic_valuationIntegerLattice_eq_top
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    [FiniteDimensional ℚ_[p] K] :
    Submodule.span ℚ_[p] (valuationIntegerLattice (K := K) (p := p) : Set K) = ⊤ := by
  obtain ⟨basis, hnorm⟩ := exists_basis_norm_le_one (p := p) (M := K)
  apply top_unique
  rw [← basis.span_eq]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact (mem_integers_iff _).mpr (hnorm i)

variable {ι : Type*} [Fintype ι]
variable (A : ι → Type*) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, ProperSpace (A i)]

def tensorIntegerRegion : Set (FinitePadicTensor (p := p) A) :=
  tensorIntegralRegion (p := p) A (fun i => (valuationIntegerLattice (K := A i) (p := p) :
    Set (A i)))

def tensorIntegerLattice : Submodule ℤ_[p] (FinitePadicTensor (p := p) A) :=
  submoduleTensorSpan (p := p) A (fun i => valuationIntegerLattice (K := A i) (p := p))

theorem isCompact_tensorIntegerRegion : IsCompact (tensorIntegerRegion (p := p) A) :=
  isCompact_tensorIntegralRegion _ _ (fun _ => isCompact_valuationIntegerLattice)

instance tensorIntegerLatticeFinite : Module.Finite ℤ_[p] (tensorIntegerLattice (p := p) A) :=
  finite_submoduleTensorSpan _ _ (fun _ => isCompact_valuationIntegerLattice)

instance tensorIntegerLatticeFree : Module.Free ℤ_[p] (tensorIntegerLattice (p := p) A) :=
  free_submoduleTensorSpan _ _ (fun _ => isCompact_valuationIntegerLattice)

theorem isCompact_tensorIntegerLattice :
    IsCompact (tensorIntegerLattice (p := p) A : Set (FinitePadicTensor (p := p) A)) :=
  isCompact_submoduleTensorSpan _ _ (fun _ => isCompact_valuationIntegerLattice)

theorem isOpen_tensorIntegerLattice :
    IsOpen (tensorIntegerLattice (p := p) A : Set (FinitePadicTensor (p := p) A)) :=
  isOpen_submoduleTensorSpan _ _ (fun _ => span_padic_valuationIntegerLattice_eq_top)

theorem padic_span_tensorIntegerLattice_eq_top :
    Submodule.span ℚ_[p] (tensorIntegerLattice (p := p) A :
      Set (FinitePadicTensor (p := p) A)) = ⊤ :=
  padic_span_submoduleTensorSpan_eq_top _ _ (fun _ => span_padic_valuationIntegerLattice_eq_top)

def integerTensorToPadicTensor :
    (PiTensorProduct ℤ_[p] (fun i => valuationIntegerLattice (K := A i) (p := p))) →ₗ[ℤ_[p]]
      FinitePadicTensor (p := p) A :=
  submoduleTensorMap (p := p) A _

theorem integerTensorToPadicTensor_injective :
    Function.Injective (integerTensorToPadicTensor (p := p) A) :=
  submoduleTensorMap_injective _ _ (fun _ => span_padic_valuationIntegerLattice_eq_top)

omit [∀ i, ProperSpace (A i)] in
theorem range_integerTensorToPadicTensor :
    LinearMap.range (integerTensorToPadicTensor (p := p) A) = tensorIntegerLattice (p := p) A :=
  range_submoduleTensorMap _ _

def integerTensorEquivLattice :
    (PiTensorProduct ℤ_[p] (fun i => valuationIntegerLattice (K := A i) (p := p))) ≃ₗ[ℤ_[p]]
      tensorIntegerLattice (p := p) A :=
  submoduleTensorEquivSpan _ _ (fun _ => span_padic_valuationIntegerLattice_eq_top)

theorem finrank_tensorIntegerLattice :
    Module.finrank ℤ_[p] (tensorIntegerLattice (p := p) A) =
      Module.finrank ℚ_[p] (FinitePadicTensor (p := p) A) :=
  finrank_of_full_integral_submodule _ (padic_span_tensorIntegerLattice_eq_top (p := p) A)

theorem tensorIntegerLattice_le_logShellLattice
    [∀ i, CharZero (A i)] [∀ i, CompleteSpace (A i)] :
    tensorIntegerLattice (p := p) A ≤ tensorLogShellLattice (p := p) A :=
  Submodule.span_mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, fun i hi => valuationIntegerLattice_le_integralLogShellLattice (hx i hi), rfl⟩)

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (A i)] [∀ i, ProperSpace (A i)] in
theorem pow_mem_tensorIntegerRegion {x : FinitePadicTensor (p := p) A}
    (hx : x ∈ tensorIntegerRegion (p := p) A) (n : ℕ) :
    x ^ n ∈ tensorIntegerRegion (p := p) A := by
  rcases hx with ⟨a, ha, rfl⟩
  refine ⟨fun i => a i ^ n, ?_, ?_⟩
  · intro i _
    exact (Integers (A i)).pow_mem (ha i (Set.mem_univ i)) n
  · symm
    have hpowers : ∀ m : ℕ, (PiTensorProduct.tprod ℚ_[p] a) ^ m =
        PiTensorProduct.tprod ℚ_[p] (fun i => a i ^ m) := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero]
        exact PiTensorProduct.one_def
      | succ m ih =>
        rw [pow_succ, ih, PiTensorProduct.tprod_mul_tprod]
        congr 1
        funext i
        exact (pow_succ (a i) m).symm
    exact hpowers n

omit [Fintype ι] in
theorem algHom_image_tensorIntegerRegion_subset_unitRegion
    [Finite ι] {J : Type*} {E : J → Type*} [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[p] (E j)]
    (f : FinitePadicTensor (p := p) A →ₐ[ℚ_[p]] ((j : J) → E j)) :
    f '' tensorIntegerRegion (p := p) A ⊆
      LeanFormal.IUT.LocalFieldProductHull.unitRegion (K := E) := by
  haveI : Fintype ι := Fintype.ofFinite ι
  have hf : Continuous f := continuous_pi (fun j =>
    ((LinearMap.proj j).comp f.toLinearMap).continuous_of_finiteDimensional)
  rintro _ ⟨x, hx, rfl⟩ j
  have hcompact := ((isCompact_tensorIntegerRegion (p := p) A).image hf).image
    (continuous_apply j)
  apply LeanFormal.IUT.LocalFieldProductHull.norm_le_one_of_compact_powers hcompact (f x j)
  intro n
  refine ⟨f (x ^ n), ⟨x ^ n, pow_mem_tensorIntegerRegion (p := p) A hx n, rfl⟩, ?_⟩
  simp only [map_pow, Pi.pow_apply]

theorem algHom_image_tensorIntegerLattice_subset_unitRegion
    {J : Type*} {E : J → Type*} [∀ j, NormedField (E j)]
    [∀ j, NormedAlgebra ℚ_[p] (E j)] [∀ j, IsUltrametricDist (E j)]
    (f : FinitePadicTensor (p := p) A →ₐ[ℚ_[p]] ((j : J) → E j)) :
    f '' (tensorIntegerLattice (p := p) A : Set (FinitePadicTensor (p := p) A)) ⊆
      LeanFormal.IUT.LocalFieldProductHull.unitRegion (K := E) := by
  let integralMap : FinitePadicTensor (p := p) A →ₗ[ℤ_[p]] ((j : J) → E j) := {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun z x => by
      change f ((z : ℚ_[p]) • x) = (z : ℚ_[p]) • f x
      exact f.toLinearMap.map_smul _ _ }
  have hspan : tensorIntegerLattice (p := p) A ≤
      (LeanFormal.IUT.LocalFieldProductHull.productIntegerLattice (p := p) (E := E)).comap
        integralMap := by
    apply Submodule.span_le.mpr
    intro x hx
    exact algHom_image_tensorIntegerRegion_subset_unitRegion (p := p) A f ⟨x, hx, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hspan hx

end

end LeanFormal.IUT.LocalFieldPadicTensor
