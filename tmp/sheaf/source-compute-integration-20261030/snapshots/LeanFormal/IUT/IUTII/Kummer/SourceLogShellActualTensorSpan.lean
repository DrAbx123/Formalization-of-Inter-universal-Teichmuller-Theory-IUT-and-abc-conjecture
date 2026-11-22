import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-!
# Actual multiple tensor products of the rational log-shell spans

Algebraic prerequisite for the IQ carrier in N4--N7 (IUT III Proposition
3.2(ii), text lines 5740--5785). The ambient object is Mathlib's universal
`PiTensorProduct`, not the image of multiplication in a common field.

The integral pure tensors generate the entire tensor product of the rational
spans. This proves the rational-generation step from the existing definition
of IQ, with no tensor-generation assumption. It does not give an identification
with the source ind-topological packet, a topology, or its decomposition as
a product of local fields. In particular it does not discharge N4--N7 alone.
-/

namespace LeanFormal.IUT

open scoped TensorProduct

section SpanGenerators

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The original generators still span after the ambient module is restricted
to their span. This includes zero and the empty generating set. -/
theorem span_subtype_originalGenerators (S : Set M) :
    Submodule.span R {x : Submodule.span R S | (x : M) ∈ S} = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨x, hx⟩ := x
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ihx => exact Submodule.smul_mem _ a ihx

/-- The set of actual pure tensors whose factors belong to the specified
integral generating sets, viewed inside the tensor product of their spans. -/
def integralSpanPureTensors {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (S : (i : ι) → Set (M i)) :
    Set (⨂[R] i, Submodule.span R (S i)) :=
  Set.range (fun x : (i : ι) → {m : Submodule.span R (S i) | (m : M i) ∈ S i} =>
    PiTensorProduct.tprod R (fun i => (x i).val))

/-- Rationalizing integral factors and then taking the actual tensor product
introduces no new generators beyond the integral pure tensors. -/
theorem integralSpanPureTensors_span_eq_top {ι : Type*} [Finite ι] {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (S : (i : ι) → Set (M i)) :
    Submodule.span R (integralSpanPureTensors (R := R) S) = ⊤ := by
  apply PiTensorProduct.submodule_span_eq_top
  intro i
  have hrange : Set.range
      (fun x : {m : Submodule.span R (S i) | (m : M i) ∈ S i} => x.val) =
      {m : Submodule.span R (S i) | (m : M i) ∈ S i} := by
    ext x
    exact ⟨fun ⟨m, hm⟩ => hm ▸ m.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  rw [hrange]
  exact span_subtype_originalGenerators (S i)

end SpanGenerators

/-- The actual tensor product of the already defined rational log-shell spans.
This construction preserves all tensor coordinates rather than multiplying
the factors into a common field. -/
abbrev SourceLogShellActualIQTensor {ι : Type*} (D : ι → SourceLogShellDatum) :=
  ⨂[ℚ] i, (D i).IQSpan

/-- Integral pure tensors in the actual IQ tensor packet. -/
def sourceLogShellActualIntegralTensors {ι : Type*} (D : ι → SourceLogShellDatum) :
    Set (SourceLogShellActualIQTensor D) :=
  integralSpanPureTensors (R := ℚ) (fun i => (D i).logShell)

/-- The integral tensor structure has the required rational span, for a finite
family of the existing log-shell data. No promise of this equality is needed. -/
theorem sourceLogShellActualIntegralTensors_span_eq_top {ι : Type*} [Finite ι]
    (D : ι → SourceLogShellDatum) :
    Submodule.span ℚ (sourceLogShellActualIntegralTensors D) = ⊤ :=
  integralSpanPureTensors_span_eq_top (fun i => (D i).logShell)

/-- Every actual IQ tensor is in the rational span of the integral tensors. -/
theorem sourceLogShellActualIQTensor_mem_span {ι : Type*} [Finite ι]
    (D : ι → SourceLogShellDatum) (x : SourceLogShellActualIQTensor D) :
    x ∈ Submodule.span ℚ (sourceLogShellActualIntegralTensors D) := by
  rw [sourceLogShellActualIntegralTensors_span_eq_top]
  trivial

end LeanFormal.IUT
