import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorUniversalProperty
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralTensorSpan

/-!
# Integral regions for tensors of finite p-adic modules

This accepts the actual regions in completion packets, which are products
of fields rather than single fields. The tensor is the topological rational
tensor constructed previously. Nonempty factors are required for full Q-span.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]

def tensorIntegralRegion (S : (i : ι) → Set (M i)) : Set (FinitePadicTensor (p := p) M) :=
  finitePadicTensorTprod (p := p) M '' Set.pi Set.univ S

theorem isCompact_tensorIntegralRegion (S : (i : ι) → Set (M i))
    (hS : ∀ i, IsCompact (S i)) : IsCompact (tensorIntegralRegion (p := p) M S) :=
  (isCompact_univ_pi hS).image (continuous_finitePadicTensorTprod (p := p) M)

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (M i)] in
theorem tensorIntegralRegion_eq_range (S : (i : ι) → Set (M i)) :
    tensorIntegralRegion (p := p) M S = Set.range (fun x : (i : ι) → S i =>
      finitePadicTensorTprod (p := p) M (fun i => (x i).val)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i => ⟨x i, hx i (Set.mem_univ i)⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => (x i).val, fun i _ => (x i).property, rfl⟩

variable [∀ i, Module ℚ (M i)] [∀ i, IsScalarTower ℚ ℚ_[p] (M i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (M i)] in
theorem rat_span_tensorIntegralRegion_eq_top [Finite ι] [Nonempty ι]
    (S : (i : ι) → Set (M i)) (hS : ∀ i, Submodule.span ℚ (S i) = ⊤) :
    Submodule.span ℚ (tensorIntegralRegion (p := p) M S) = ⊤ := by
  rw [tensorIntegralRegion_eq_range]
  exact LocalFieldIntegralTensorSpan.rat_span_integralTensors_eq_top (k := ℚ_[p]) S hS

end

end LeanFormal.IUT.LocalFieldPadicTensor
