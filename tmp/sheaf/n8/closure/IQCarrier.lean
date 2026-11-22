import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan

/-!
# N8 actual IQ carrier

For an index family `D : ι → SourceLogShellDatum`, the N8 IQ carrier is the
actual rational tensor product of the existing `IQSpan` submodules:

  `N8IQCarrier D = ⨂[ℚ] i, (D i).IQSpan`.

This is the actual `PiTensorProduct` carrier, not a product of fields and not
a fresh product-of-fields model.  The integral pure tensors and their rational
spanning theorem are the existing actual tensor-span lemmas, reused directly.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.IQCarrier

open LeanFormal.IUT

universe u

/-- The N8 actual IQ carrier: rational tensor product of the existing
`SourceLogShellDatum.IQSpan` coordinates. -/
abbrev N8IQCarrier {ι : Type u} (D : ι → SourceLogShellDatum) : Type u :=
  SourceLogShellActualIQTensor D

/-- The actual integral pure tensors in the N8 IQ carrier (reused donor). -/
def N8IntegralPureTensors {ι : Type u} (D : ι → SourceLogShellDatum) :
    Set (N8IQCarrier D) :=
  sourceLogShellActualIntegralTensors D

/-- The integral pure tensors have full rational span in the N8 IQ carrier. -/
theorem N8IntegralPureTensors_span_eq_top {ι : Type u} [Finite ι]
    (D : ι → SourceLogShellDatum) :
    Submodule.span ℚ (N8IntegralPureTensors D) = ⊤ :=
  sourceLogShellActualIntegralTensors_span_eq_top D

/-- Every N8 IQ tensor lies in the rational span of the integral pure tensors. -/
theorem N8IQCarrier_mem_span {ι : Type u} [Finite ι]
    (D : ι → SourceLogShellDatum) (x : N8IQCarrier D) :
    x ∈ Submodule.span ℚ (N8IntegralPureTensors D) := by
  rw [N8IntegralPureTensors_span_eq_top]
  trivial

end LeanFormal.IUT.N8Closure.IQCarrier