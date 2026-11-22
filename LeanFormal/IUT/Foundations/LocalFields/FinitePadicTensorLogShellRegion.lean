import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorUniversalProperty
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitPerfectionIndTopology

/-!
# Actual logarithmic integral regions in the finite tensor

Take pure tensors of the constructed integral unit logarithmic shells.
Their image is compact and contains the tensor identity. For a nonempty
factor family their rational span is the entire genuine tensor.
No positive measure of the pure-tensor image itself is asserted.
-/

namespace LeanFormal.IUT.LocalFieldPadicTensor

open LeanFormal.IUT.LocalFieldIntegralUnits LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (A : ι → Type*) [∀ i, NormedField (A i)] [∀ i, NormedAlgebra ℚ_[p] (A i)]
variable [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable [∀ i, CharZero (A i)] [∀ i, IsUltrametricDist (A i)]
variable [∀ i, CompleteSpace (A i)] [∀ i, ProperSpace (A i)]

def tensorLogShellRegion : Set (FinitePadicTensor (p := p) A) :=
  finitePadicTensorTprod (p := p) A ''
    Set.pi Set.univ (fun i => (integralLogShell (K := A i) (p := p) : Set (A i)))

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem tensorLogShellRegion_eq_range : tensorLogShellRegion (p := p) A =
    Set.range (fun x : (i : ι) → integralLogShell (K := A i) (p := p) =>
      finitePadicTensorTprod (p := p) A (fun i => (x i).val)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun i => ⟨x i, hx i (Set.mem_univ i)⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨fun i => (x i).val, fun i _ => (x i).property, rfl⟩

theorem isCompact_tensorLogShellRegion : IsCompact (tensorLogShellRegion (p := p) A) :=
  (isCompact_univ_pi (fun i => isCompact_integralLogShell (K := A i) (p := p))).image
    (continuous_finitePadicTensorTprod (p := p) A)

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem one_mem_tensorLogShellRegion :
    (1 : FinitePadicTensor (p := p) A) ∈ tensorLogShellRegion (p := p) A := by
  refine ⟨fun _ => 1, ?_, ?_⟩
  · intro i _
    exact integers_subset_integralLogShell (p := p) ((Integers (A i)).one_mem)
  · rfl

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem tensorLogShellRegion_nonempty : (tensorLogShellRegion (p := p) A).Nonempty :=
  ⟨1, one_mem_tensorLogShellRegion A⟩

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem rat_span_integralLogShell_eq_top (i : ι) :
    Submodule.span ℚ (integralLogShell (K := A i) (p := p) : Set (A i)) = ⊤ := by
  have hp : ‖(p : A i)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] (A i)), norm_algebraMap', Padic.norm_p]
    have hpone : (1 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    exact inv_lt_one_of_one_lt₀ hpone
  have hball := LocalFieldIntegralTensorSpan.rat_span_unitBall_eq_top
    (K := A i) p (Fact.out : Nat.Prime p).ne_zero hp
  apply top_unique
  rw [← hball]
  apply Submodule.span_mono
  intro x hx
  apply integers_subset_integralLogShell (p := p)
  exact (mem_integers_iff _).mpr (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx)

omit [Fintype ι] [∀ i, FiniteDimensional ℚ_[p] (A i)] in
theorem rat_span_tensorLogShellRegion_eq_top [Finite ι] [Nonempty ι] :
    Submodule.span ℚ (tensorLogShellRegion (p := p) A) = ⊤ := by
  rw [tensorLogShellRegion_eq_range]
  exact LocalFieldIntegralTensorSpan.rat_span_integralTensors_eq_top
    (k := ℚ_[p]) _ (rat_span_integralLogShell_eq_top A)

section ActualFiniteLayers

variable {Ω : ι → Type*} [∀ i, NormedField (Ω i)] [∀ i, IsUltrametricDist (Ω i)]
variable [∀ i, NormedAlgebra ℚ_[p] (Ω i)]

theorem isCompact_finiteSubfield_tensorLogShellRegion
    (F : (i : ι) → FiniteLocalSubfield p (Ω i)) :
    IsCompact (tensorLogShellRegion (p := p) (fun i => (F i).val)) :=
  isCompact_tensorLogShellRegion _

end ActualFiniteLayers

end

end LeanFormal.IUT.LocalFieldPadicTensor
